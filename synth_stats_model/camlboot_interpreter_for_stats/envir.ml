open Asttypes
(* open Conf *)
open Data

let empty_env =
  { values = [];
    modules = [];
    constructors = [];
    classes = [];
    current_object = None;
  }

let env_set_value key _v env =
  { env with values =  (key.txt, (true, None, Value (ref None, key.loc))) :: env.values }

let env_set_lvar lvar obj env =
  { env with values =
                (lvar, (false, None, Instance_variable (obj, lvar))) :: env.values }

let env_set_instance_variable key obj v env =
  { env with values =  (key, (true, None, Instance_variable (obj, v))) :: env.values }

let env_set_module key m env =
  { env with modules =  (key, (true, None, m)) :: env.modules }

let env_set_constr key c env =
  { env with constructors =  (key, (true, None, c)) :: env.constructors }

let env_set_class key cl env =
  { env with classes =  (key, (true, None, cl)) :: env.classes }


let append_lident_opts lid_opt1 lid_opt2 =
  let flatten_lident_opt = function Some lid -> Longident.flatten lid | None -> [] in
  Longident.unflatten begin
    flatten_lident_opt lid_opt1 @
    flatten_lident_opt lid_opt2
  end

let env_extend incoming_mod_lident_option exported env1 data =
  let merge l l' =
    List.fold_right (fun (k, (lident_opt, v)) l ->  (k, (exported, append_lident_opts incoming_mod_lident_option lident_opt, v)) :: l) l' l
  in
  let values l = List.map (fun (k, (lid_opt, intro_loc)) -> (k, (lid_opt, Value (ref None, intro_loc)))) l in
  { values = merge env1.values (values data.mod_values);
    modules = merge env1.modules data.mod_modules;
    constructors = merge env1.constructors data.mod_constructors;
    classes = merge env1.classes data.mod_classes;
    current_object = env1.current_object;
  }

let declare_unit env unit_path =
  let module_name = module_name_of_unit_path unit_path in
  let unit_id = Path unit_path in
  let unit_mod = Unit (unit_id, ref Not_initialized_yet) in
  let modules = (module_name, (true, None, unit_mod)) :: env.modules in
  { env with modules; }

let define_unit env unit_path mdl =
  let module_name = module_name_of_unit_path unit_path in
  match List.assoc module_name env.modules with
    | exception Not_found ->
       Format.kasprintf invalid_arg
         "define_unit: The module unit %s is not yet declared"
         module_name
    | (_, _, (Module _ | Functor _)) ->
       Format.kasprintf invalid_arg
         "define_unit: The module %s is not a unit"
         module_name
    | (_, _, Unit (unit_id, unit_state)) ->
       begin match !unit_state with
         | Initialized _ ->
            Format.kasprintf invalid_arg
              "define_unit: The module unit %a is already defined"
              pp_print_unit_id unit_id
         | Not_initialized_yet ->
            unit_state := Initialized mdl;
            env
       end

let env_of_module_data mod_data =
  env_extend None true empty_env mod_data

let make_module_data env =
  let exported env_map =
    env_map |> List.filter (fun (_ ,(b, _, _)) -> b) |> List.map (fun (k, (_, lid_opt, v)) -> (k, (lid_opt, v)))
  in
  let values env_map =
    env_map
    |> List.filter (function
          | (_, (_, Value _v)) -> true
          | (_, (_, Instance_variable _)) -> false)
    |> List.map (function
           | (name, (lid_opt, Value (_, intro_loc))) -> (name, (lid_opt, intro_loc))
           | (_, (_, Instance_variable _)) -> assert false) in
  {
    mod_values = values (exported env.values);
    mod_modules = exported env.modules;
    mod_constructors = exported env.constructors;
    mod_classes = exported env.classes;
  }

let prevent_export env =
  let prevent env_map = List.map (fun (k, (_, lid_opt, v)) -> (k, (false, lid_opt, v))) env_map in
  { values = prevent env.values;
    modules = prevent env.modules;
    constructors = prevent env.constructors;
    classes = prevent env.classes;
    current_object = env.current_object;
  }

(* let decompose get_module_data env { txt = lident; loc } =
  match lident with
  | Longident.Lapply _ -> failwith "Lapply lookups not supported"
  | Longident.Lident str -> ("env", None, env, str)
  | Longident.Ldot (ld, str) ->
    let new_prefix, md = get_module_data env { txt = ld; loc } in
    ("module", new_prefix, env_of_module_data md, str) *)

let lookup object_name ~env_name new_prefix object_env { txt = str; loc } =
  try let (_, source_mod_path, thing) = List.assoc str object_env in (append_lident_opts source_mod_path new_prefix, thing)
  with Not_found ->
    Format.eprintf
      "%a@.%s not found in %s: %s@."
      Location.print_loc
      loc
      (String.capitalize_ascii object_name)
      env_name
      str;
    raise Not_found

let rec env_get_module env ({ loc; _ } as lid) =
  match lid.txt with
  | Longident.Lapply _ -> failwith "Lapply lookups not supported"
  | Longident.Lident name -> lookup "module" ~env_name:"env" (Some lid.txt) env.modules { txt = name; loc }
  | Longident.Ldot (ld, name) ->
    let new_prefix, md = env_get_module_data env { txt = ld; loc } in
    lookup "module" ~env_name:"module" new_prefix (env_of_module_data md).modules { txt = name; loc }

  (* let env_name, new_prefix, env, id = decompose env_get_module_data env lid in
  lookup "module" ~env_name new_prefix env.modules { txt = id; loc } *)

and env_get_value_or_lvar env ({ loc; _ } as lid) =
  match lid.txt with
  | Longident.Lapply _ -> failwith "Lapply lookups not supported"
  | Longident.Lident name -> lookup "value" ~env_name:"env" None env.values { txt = name; loc }
  | Longident.Ldot (ld, name) ->
    let new_prefix, md = env_get_module_data env { txt = ld; loc } in
    lookup "value" ~env_name:"module" new_prefix (env_of_module_data md).values { txt = name; loc }

  (* let env_name, new_prefix, env, id = decompose env_get_module_data env lid in
  lookup "value" ~env_name new_prefix env.values { txt = id; loc } *)

and env_get_constr env ({ loc; _ } as lid) =
  match lid.txt with
  | Longident.Lapply _ -> failwith "Lapply lookups not supported"
  | Longident.Lident name -> lookup "constructor" ~env_name:"env" None env.constructors { txt = name; loc }
  | Longident.Ldot (ld, name) ->
    let new_prefix, md = env_get_module_data env { txt = ld; loc } in
    lookup "constructor" ~env_name:"module" new_prefix (env_of_module_data md).constructors { txt = name; loc }

  (* let env_name, new_prefix, env, id = decompose env_get_module_data env lid in
  lookup "constructor" ~env_name new_prefix env.constructors { txt = id; loc } *)

and env_get_class env ({ loc; _ } as lid) =
  match lid.txt with
  | Longident.Lapply _ -> failwith "Lapply lookups not supported"
  | Longident.Lident name -> lookup "class" ~env_name:"env" None env.classes { txt = name; loc }
  | Longident.Ldot (ld, name) ->
    let new_prefix, md = env_get_module_data env { txt = ld; loc } in
    lookup "class" ~env_name:"module" new_prefix (env_of_module_data md).classes { txt = name; loc }

    (* let env_name, new_prefix, env, id = decompose env_get_module_data env lid in
  lookup "class" ~env_name new_prefix env.classes { txt = id; loc } *)

and env_get_module_data env ({ loc; _ } as id) =
  get_module_data loc (env_get_module env id)
