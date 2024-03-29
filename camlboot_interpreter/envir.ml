open Asttypes
(* open Conf *)
open Data

let empty_env =
  { values = SMap.empty;
    modules = SMap.empty;
    constructors = SMap.empty;
    classes = SMap.empty;
    current_object = None;
  }

let env_set_value key v env =
  { env with values = SMap.add key (true, Value v) env.values }

let env_set_lvar lvar obj env =
  { env with values =
               SMap.add lvar (false, Instance_variable (obj, lvar)) env.values }

let env_set_instance_variable key obj v env =
  { env with values = SMap.add key (true, Instance_variable (obj, v)) env.values }

let env_set_module key m env =
  { env with modules = SMap.add key (true, m) env.modules }

let env_set_constr key c env =
  { env with constructors = SMap.add key (true, c) env.constructors }

let env_set_class key cl env =
  { env with classes = SMap.add key (true, cl) env.classes }

let env_extend exported env1 data =
  let merge s1 s2 =
    SMap.fold (fun k v env -> SMap.add k (exported, v) env) s2 s1
  in
  let values s = SMap.map (fun v -> Value v) s in
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
  let modules = SMap.add module_name (true, unit_mod) env.modules in
  { env with modules; }

let define_unit env unit_path mdl =
  let module_name = module_name_of_unit_path unit_path in
  match SMap.find module_name env.modules with
    | exception Not_found ->
       Format.kasprintf invalid_arg
         "define_unit: The module unit %s is not yet declared"
         module_name
    | (_, (Module _ | Functor _)) ->
       Format.kasprintf invalid_arg
         "define_unit: The module %s is not a unit"
         module_name
    | (_, Unit (unit_id, unit_state)) ->
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
  env_extend true empty_env mod_data

let make_module_data env =
  let exported env_map =
    env_map |> SMap.filter (fun _ (b, _) -> b) |> SMap.map snd
  in
  let values env_map =
    env_map
    |> SMap.filter (fun _ -> function
          | Value _v -> true
          | Instance_variable _ -> false)
    |> SMap.map (function
           | Value v -> v
           | Instance_variable _ -> assert false) in
  {
    mod_values = values (exported env.values);
    mod_modules = exported env.modules;
    mod_constructors = exported env.constructors;
    mod_classes = exported env.classes;
    mod_internal_env = env;
  }

let prevent_export env =
  let prevent env_map = SMap.map (fun (_, x) -> (false, x)) env_map in
  { values = prevent env.values;
    modules = prevent env.modules;
    constructors = prevent env.constructors;
    classes = prevent env.classes;
    current_object = env.current_object;
  }

let decompose get_module_data env { txt = lident; loc } =
  match lident with
  | Longident.Lapply _ -> failwith "Lapply lookups not supported"
  | Longident.Lident str -> ("env", env, str)
  | Longident.Ldot (ld, str) ->
    let md = get_module_data env { txt = ld; loc } in
    ("module", env_of_module_data md, str)

let lookup _object_name ~env_name object_env { txt = str; loc = _loc } =
  let _ = env_name in
  try snd (SMap.find str object_env)
  with Not_found ->
    (* Format.eprintf
      "%a@.%s not found in %s: %s@."
      Location.print_loc
      loc
      (String.capitalize_ascii object_name)
      env_name
      str; *)
    raise Not_found

let rec env_get_module env ({ loc; _ } as lid) =
  let env_name, env, id = decompose env_get_module_data env lid in
  lookup "module" ~env_name env.modules { txt = id; loc }

and env_get_value_or_lvar env ({ loc; _ } as lid) =
  let env_name, env, id = decompose env_get_module_data env lid in
  lookup "value" ~env_name env.values { txt = id; loc }

and env_get_constr env ({ loc; _ } as lid) =
  let env_name, env, id = decompose env_get_module_data env lid in
  lookup "constructor" ~env_name env.constructors { txt = id; loc }

and env_get_class env ({ loc; _ } as lid) =
  let env_name, env, id = decompose env_get_module_data env lid in
  lookup "class" ~env_name env.classes { txt = id; loc }

and env_get_module_data env ({ loc; _ } as id) =
  get_module_data loc (env_get_module env id)
