
(* May not need this. Typedtree tracks binding locations via uniquely stamped Idents *)

(* let (restore_names, old) = assign_unique_names old in *)
open Asttypes
open Parsetree
open Shared.Ast
open Shared.Util

(* Functors, first-class modules, and recursive modules not supported. *)
(* Also not tracking named types or polymorphic variants. *)
(* But are tracking field labels and ctor names (including exceptions). *)
(* Additionally, module signatures are ignored and all module top-level items are considered exported. (It appears Camlboot_interpreter also ignores signatures.) *)


module StaticEnv = struct
  type t =
    (* bool indicates if the item should be exported from the module *)
    { values : (bool * Location.t) SMap.t
    ; mods   : (bool * t * Location.t) SMap.t
    ; ctors  : (bool * Location.t) SMap.t
    ; labels : (bool * Location.t) SMap.t (* Record field names...all smooshed together *)
    }

  let empty =
    { values = SMap.empty
    ; mods   = SMap.empty
    ; ctors  = SMap.empty
    ; labels = SMap.empty
    }

  (* Returns (module env in which to perform lookup, name to look up) *)
  let rec decompose_lid env = function
    | Longident.Lident name      -> (env, name)
    | Longident.Ldot (lid, name) -> (get_mod_env_by_lid env lid, name)
    | Longident.Lapply _         -> failwith "StaticEnv.decompose_lid can't lookup in functors"
  and get_mod_env_by_lid env lid =
    let (env, name) = decompose_lid env lid in
    SMap.find name env.mods
    |> fun (_, mod_env, _) -> mod_env

  let get_value_loc_by_lid env lid =
    let (env, name) = decompose_lid env lid in
    SMap.find name env.values
    |> fun (_, loc) -> loc
  let get_mod_loc_by_lid env lid =
    let (env, name) = decompose_lid env lid in
    SMap.find name env.mods
    |> fun (_, _, loc) -> loc
  let get_ctor_loc_by_lid env lid =
    let (env, name) = decompose_lid env lid in
    SMap.find name env.ctors
    |> fun (_, loc) -> loc
  let get_label_loc_by_lid env lid =
    let (env, name) = decompose_lid env lid in
    SMap.find name env.labels
    |> fun (_, loc) -> loc

  let rec equal env1 env2 =
    SMap.equal (=) env1.values env2.values &&
    SMap.equal (=) env1.ctors  env2.ctors  &&
    SMap.equal (=) env1.labels env2.labels &&
    let mods_equal (b1, mod1, loc1) (b2, mod2, loc2) =
      b1 = b2 && loc1 = loc2 && equal mod1 mod2 in
    SMap.equal mods_equal env1.mods env2.mods

  (* Prefer items in env' *)
  let extend env env' =
    { values = SMap.union (fun _ _ v' -> Some v') env.values env'.values
    ; mods   = SMap.union (fun _ _ v' -> Some v') env.mods   env'.mods
    ; ctors  = SMap.union (fun _ _ v' -> Some v') env.ctors  env'.ctors
    ; labels = SMap.union (fun _ _ v' -> Some v') env.labels env'.labels
    }

  let exported_only env =
    { values = SMap.filter (fun _ (is_exported, _)    -> is_exported) env.values
    ; mods   = SMap.filter (fun _ (is_exported, _, _) -> is_exported) env.mods
    ; ctors  = SMap.filter (fun _ (is_exported, _)    -> is_exported) env.ctors
    ; labels = SMap.filter (fun _ (is_exported, _)    -> is_exported) env.labels
    }

  let dont_export env =
    { values = SMap.map (fun (_,    loc) -> (false,    loc)) env.values
    ; mods   = SMap.map (fun (_, t, loc) -> (false, t, loc)) env.mods
    ; ctors  = SMap.map (fun (_,    loc) -> (false,    loc)) env.ctors
    ; labels = SMap.map (fun (_,    loc) -> (false,    loc)) env.labels
    }

  let add_value ?(exported = true) name_loced env =
    { env with values = SMap.add name_loced.txt (exported, name_loced.loc) env.values }

  let add_pat ?(exported = true) pat env =
    let pat_names_loced = Pat.names_loced pat in
    let add_name env name_loced = add_value ~exported name_loced env in
    List.fold_left add_name env pat_names_loced

  let add_mod ?(exported = true) name_loced mod_env env =
    { env with mods = SMap.add name_loced.txt (exported, mod_env, name_loced.loc) env.mods }

  let add_ctor ?(exported = true) name_loced env =
    { env with ctors = SMap.add name_loced.txt (exported, name_loced.loc) env.ctors }

  let add_label ?(exported = true) name_loced env =
    { env with labels = SMap.add name_loced.txt (exported, name_loced.loc) env.labels }
end

(* For handling cyclic references between modules the program may be iterated over multiple times so these functions should be robust to that. *)
type iter_funs =
  { define_value : string Location.loc -> unit
  ; define_ctor  : string Location.loc -> unit
  ; define_mod   : string Location.loc -> unit
  ; define_label : string Location.loc -> unit
  ; use_value    : StaticEnv.t -> Longident.t Location.loc -> unit
  ; use_mod      : StaticEnv.t -> Longident.t Location.loc -> unit
  ; use_ctor     : StaticEnv.t -> Longident.t Location.loc -> unit
  ; use_label    : StaticEnv.t -> Longident.t Location.loc -> unit
  }

let dummy_iter_funs =
  { define_value = (fun _ -> ())
  ; define_ctor  = (fun _ -> ())
  ; define_mod   = (fun _ -> ())
  ; define_label = (fun _ -> ())
  ; use_value    = (fun _ _ -> ())
  ; use_mod      = (fun _ _ -> ())
  ; use_ctor     = (fun _ _ -> ())
  ; use_label    = (fun _ _ -> ())
  }

let rec iter_struct_item fs env struct_item =
  let open StaticEnv in
  match struct_item.pstr_desc with
  | Pstr_eval (e, _) -> iter_exp fs env e; env
  | Pstr_value (rec_flag, vbs) -> iter_vbs fs env rec_flag vbs
  | Pstr_primitive value_desc -> fs.define_value value_desc.pval_name; add_value value_desc.pval_name env
  | Pstr_type (_, types) ->
    let ctor_decls  = types |>@@ (fun typ -> match typ.ptype_kind with Ptype_variant ctor_decls -> ctor_decls  | _ -> []) in
    let label_decls = types |>@@ (fun typ -> match typ.ptype_kind with Ptype_record label_decls -> label_decls | _ -> []) in
    ctor_decls
    |> List.fold_left
      (fun env ctor -> fs.define_ctor ctor.pcd_name; add_ctor ctor.pcd_name env)
      env
    |> begin fun env' ->
      List.fold_left
        (fun env label -> fs.define_label label.pld_name; add_label label.pld_name env)
        env'
        label_decls
    end
  | Pstr_typext _ -> env
  | Pstr_exception { pext_name; pext_kind = Pext_decl _; _ } ->
    fs.define_ctor pext_name;
    add_ctor pext_name env
  | Pstr_exception { pext_name; pext_kind = Pext_rebind lid_loced; _ } ->
    fs.use_ctor env lid_loced;
    fs.define_ctor pext_name;
    add_ctor pext_name env
  | Pstr_module { pmb_name; pmb_expr = mod_exp; _ } ->
    let mod_env = exported_only (iter_mod_exp fs (dont_export env) mod_exp) in
    fs.define_mod pmb_name;
    add_mod pmb_name mod_env env
  | Pstr_modtype _ -> env
  | Pstr_open { popen_lid = lid_loced; _ } ->
    fs.use_mod env lid_loced;
    extend env (dont_export (get_mod_env_by_lid env lid_loced.txt))
  | Pstr_include { pincl_mod = mod_exp; _ } ->
    let mod_env = exported_only (iter_mod_exp fs (dont_export env) mod_exp) in
    extend env mod_env
  | Pstr_attribute  _ -> env
  | Pstr_recmodule  _ -> failwith "Pstr_recmodule not supported"
  | Pstr_class      _ -> failwith "Pstr_class not supported"
  | Pstr_class_type _ -> failwith "Pstr_class_type not supported"
  | Pstr_extension  _ -> failwith "Pstr_extension not supported"

and iter_structure fs env struct_items =
  StaticEnv.exported_only (List.fold_left (iter_struct_item fs) env struct_items)
and iter_vbs fs env rec_flag vbs =
  let open StaticEnv in
  let env' = vbs |>@ Vb.pat |> List.fold_left (fun env pat -> add_pat pat env) env in
  let binding_env = match rec_flag with Recursive -> env' | _ -> env in
  vbs |> List.iter (fun vb -> iter_pat fs binding_env (Vb.pat vb); iter_exp fs binding_env (Vb.exp vb));
  env'
and iter_exp fs env { pexp_desc; _ } =
  let iter_exp_opt fs env exp_opt = exp_opt |>& iter_exp fs env ||& () in
  let iter_case fs env { pc_lhs; pc_guard; pc_rhs } =
    iter_pat fs env pc_lhs;
    let env' = StaticEnv.add_pat pc_lhs env in
    iter_exp_opt fs env' pc_guard;
    iter_exp fs env' pc_rhs in
  match pexp_desc with
  | Pexp_ident lid_loced -> fs.use_value env lid_loced
  | Pexp_constant _ -> ()
  | Pexp_let (rec_flag, vbs, exp) -> iter_exp fs (iter_vbs fs env rec_flag vbs) exp
  | Pexp_function cases -> List.iter (iter_case fs env) cases
  | Pexp_fun (_, arg_default_opt, pat, exp) ->
    iter_exp_opt fs env arg_default_opt;
    iter_pat fs env pat;
    iter_exp fs (StaticEnv.add_pat pat env) exp
  | Pexp_apply (f_exp, args) ->
    iter_exp fs env f_exp;
    args |> List.iter (fun (_, arg_exp) -> iter_exp fs env arg_exp)
  | Pexp_match (exp, cases)
  | Pexp_try   (exp, cases) ->
    iter_exp fs env exp;
    List.iter (iter_case fs env) cases
  | Pexp_tuple exps -> List.iter (iter_exp fs env) exps
  | Pexp_construct (lid_loced, exp_opt) ->
    fs.use_ctor env lid_loced;
    iter_exp_opt fs env exp_opt
  | Pexp_variant (_, exp_opt) -> iter_exp_opt fs env exp_opt
  | Pexp_record (fields, exp_opt) ->
    iter_exp_opt fs env exp_opt;
    fields |> List.iter (fun (lid_loced, exp) -> fs.use_label env lid_loced; iter_exp fs env exp)
  | Pexp_field (exp, lid_loced) ->
    iter_exp fs env exp;
    fs.use_label env lid_loced
  | Pexp_setfield (e_lhs, lid_loced, e_rhs) ->
    iter_exp fs env e_lhs;
    fs.use_label env lid_loced;
    iter_exp fs env e_rhs
  | Pexp_array exps -> List.iter (iter_exp fs env) exps
  | Pexp_ifthenelse (e1, e2, e_opt) ->
    iter_exp fs env e1;
    iter_exp fs env e2;
    iter_exp_opt fs env e_opt
  | Pexp_sequence (e1, e2)
  | Pexp_while    (e1, e2) ->
    iter_exp fs env e1;
    iter_exp fs env e2
  | Pexp_for (pat, e_start, e_end, _, e) ->
    iter_pat fs env pat;
    iter_exp fs env e_start;
    iter_exp fs env e_end;
    iter_exp fs (StaticEnv.add_pat ~exported:false pat env) e
  | Pexp_constraint (exp, _)
  | Pexp_coerce (exp, _, _)  -> iter_exp fs env exp
  | Pexp_send (_, _)         -> failwith "Pexp_send not supported"
  | Pexp_new _               -> failwith "Pexp_new not supported"
  | Pexp_setinstvar (_, _)   -> failwith "Pexp_setinstvar not supported"
  | Pexp_override _          -> failwith "Pexp_override not supported"
  | Pexp_letmodule (name_loced, mod_exp, exp) ->
    let open StaticEnv in
    fs.define_mod name_loced;
    let mod_env = exported_only (iter_mod_exp fs (dont_export env) mod_exp) in
    let env' = add_mod name_loced mod_env env in
    iter_exp fs env' exp
  | Pexp_letexception ({ pext_name; pext_kind = Pext_decl _; _ }, exp) ->
    fs.define_ctor pext_name;
    iter_exp fs (StaticEnv.add_ctor pext_name env) exp
  | Pexp_letexception ({ pext_name; pext_kind = Pext_rebind lid_loced; _ }, exp) ->
    fs.use_mod env lid_loced;
    fs.define_ctor pext_name;
    iter_exp fs (StaticEnv.add_ctor pext_name env) exp
  | Pexp_assert exp
  | Pexp_lazy exp-> iter_exp fs env exp
  | Pexp_open (_, lid_loced, exp) ->
    fs.use_mod env lid_loced;
    let open StaticEnv in
    let mod_env = get_mod_env_by_lid env lid_loced.txt in
    iter_exp fs (extend env (dont_export (exported_only mod_env))) exp
  | Pexp_unreachable    -> ()
  | Pexp_extension _    -> failwith "Pexp_extension not supported"
  | Pexp_poly (_, _)    -> failwith "Pexp_poly not supported"
  | Pexp_object _       -> failwith "Pexp_object not supported"
  | Pexp_newtype (_, _) -> failwith "Pexp_newtype not supported"
  | Pexp_pack _         -> failwith "Pexp_pack not supported"

and iter_pat fs env pat =
  List.iter fs.define_value (Pat.names_loced pat);
  let rec iter_pat fs env pat =
    let recurse = iter_pat fs env in
    match pat.ppat_desc with
    | Ppat_any               -> ()
    | Ppat_var _             -> ()
    | Ppat_alias (p, _)      -> recurse p
    | Ppat_constant _        -> ()
    | Ppat_interval (_, _)   -> ()
    | Ppat_tuple ps          -> List.iter recurse ps
    | Ppat_construct (lid_loced, p_opt) ->
      fs.use_ctor env lid_loced;
      p_opt |>& recurse ||& ()
    | Ppat_variant (_, p_opt) -> p_opt |>& recurse ||& ()
    (* can't just use Pat.iter b/c of Ppat_open *)
    | Ppat_record (fields, _) ->
      fields |> List.iter (fun (lid_loced, p) -> fs.use_label env lid_loced; recurse p)
    | Ppat_array ps          -> List.iter recurse ps
    | Ppat_or (p1, p2)       -> recurse p1; recurse p2
    | Ppat_constraint (p, _) -> recurse p
    | Ppat_type _            -> () (* Not handling types yet *)
    | Ppat_lazy p            -> recurse p
    | Ppat_unpack _          -> () (* Not handling first class modules *)
    | Ppat_exception p       -> recurse p
    | Ppat_extension _       -> () (* Not handling extensions *)
    | Ppat_open (lid_loced, p) ->
      fs.use_mod env lid_loced;
      let open StaticEnv in
      let mod_env = get_mod_env_by_lid env lid_loced.txt in
      iter_pat fs (extend env (dont_export (exported_only mod_env))) p in
  iter_pat fs env pat

and iter_mod_exp fs env mod_exp =
  StaticEnv.exported_only @@
  match mod_exp.pmod_desc with
  | Pmod_ident lid_loced                               -> fs.use_mod env lid_loced; StaticEnv.get_mod_env_by_lid env lid_loced.txt
  | Pmod_structure struct_items                        -> iter_structure fs env struct_items
  | Pmod_constraint (mod_exp, _)                       -> iter_mod_exp fs env mod_exp
  | Pmod_functor ({ txt = _arg_name; _ }, _, _mod_exp) -> failwith "Pmod_functor not supported"
  | Pmod_apply (_, _)                                  -> failwith "Pmod_apply not supported"
  | Pmod_unpack _                                      -> failwith "Pmod_unpack not supported"
  | Pmod_extension _                                   -> failwith "Pmod_extension not supported"

(* Hmm...to handle cyclic references between modules...just iterate until a fixpoint? *)
let rec iter_rec_units fs env flags_and_units =
  let new_env actually_iterate =
    List.fold_left
      (fun unit_env (flags, unit_path, parsed) ->
        let open_env env flag =
          match flag with
          | Camlboot_interpreter.Interp.Open module_lid ->
            try StaticEnv.(extend env (exported_only (get_mod_env_by_lid env module_lid)))
            with Not_found -> env in
        let init_mod_env = List.fold_left open_env unit_env flags in
        let mod_env = iter_structure (if actually_iterate then fs else dummy_iter_funs) init_mod_env parsed in
        let mod_name = Camlboot_interpreter.Data.module_name_of_unit_path unit_path in
        let mod_loc = Location.in_file unit_path in
        { unit_env with mods = SMap.add mod_name (false, mod_env, mod_loc) unit_env.mods }
      )
      env
      flags_and_units
  in
  let env' = new_env false in
  if StaticEnv.equal env env'
  then new_env true
  else iter_rec_units fs env' flags_and_units

let binding_map_and_free flags_and_units =
  let free = ref [] in
  let uses = ref [] in
  let use getter env lid_loced =
    try
      let def_loc = getter env lid_loced.txt in
      uses := (def_loc, lid_loced.loc)::!uses
    with
      Not_found -> free := lid_loced.loc::!free
  in
  let iter_funs =
    { dummy_iter_funs with
      use_value = use StaticEnv.get_value_loc_by_lid
    ; use_mod   = use StaticEnv.get_mod_loc_by_lid
    ; use_ctor  = use StaticEnv.get_ctor_loc_by_lid
    ; use_label = use StaticEnv.get_label_loc_by_lid
    } in
  ignore @@ iter_rec_units iter_funs StaticEnv.empty flags_and_units;
  !uses, !free

(* Var names only. *)
let free_var_lids_in_exp exp =
  let free = ref [] in
  let use getter env lid_loced =
    try
      ignore (getter env lid_loced.txt)
    with
      Not_found -> free := lid_loced.txt::!free
  in
  let iter_funs =
    { dummy_iter_funs with
      use_value = use StaticEnv.get_value_loc_by_lid
    } in
  ignore @@ iter_exp iter_funs StaticEnv.empty exp;
  !free


(* Terminal names used or defined. *)
let names_seen flags_and_units =
  let nameset            = ref SSet.empty in
  let define name_loced  = nameset := SSet.add name_loced.txt                 !nameset in
  let use _env lid_loced = nameset := SSet.add (Longident.last lid_loced.txt) !nameset in
  let iter_funs =
    { define_value = define
    ; define_mod   = define
    ; define_ctor  = define
    ; define_label = define
    ; use_value    = use
    ; use_mod      = use
    ; use_ctor     = use
    ; use_label    = use
    } in
  ignore @@ iter_rec_units iter_funs StaticEnv.empty flags_and_units;
  !nameset

(* module Name = struct
  (* Generates a name not used or defined in the given programs. *)
  (* May shadow imported names not used or defined in flags_and_units, but otherwise conservative. *)
  let gen ?(base_name = "var") flags_and_units =
    let nameset = names_seen flags_and_units in
    let name = ref base_name in
    let n    = ref 2 in
    while SSet.mem !name nameset do
      name := base_name ^ string_of_int !n;
      incr n
    done;
    !name
end

 *)
