open Parsetree
open Shared.Ast
open Shared.Util

(* Merge with Name.ml? *)

(* Also searches in [@vis] attributes. *)
let rec free_unqualified_names ?(fillings = Shared.Loc_map.empty) exp =
  let recurse = free_unqualified_names ~fillings in
  let free_unqualified_names_case { pc_lhs; pc_guard; pc_rhs } =
    List.diff
      (free_unqualified_names_pat pc_lhs @ (pc_guard |>& recurse ||& []) @ recurse pc_rhs)
      (Pat.names pc_lhs)
  in
  names_in_vis_attrs exp.pexp_attributes @
  match Shared.Loc_map.find_opt exp.pexp_loc fillings with
  | Some filling_exp -> recurse filling_exp
  | None ->
    begin match exp.pexp_desc with
    | Pexp_ident { txt = Longident.Lident name; _ }
    | Pexp_new   { txt = Longident.Lident name; _ } ->
      [name]
    | Pexp_ident { txt = _; _ }
    | Pexp_new   { txt = _; _ }
    | Pexp_constant _
    | Pexp_extension _
    | Pexp_unreachable ->
      []
    | Pexp_let (Asttypes.Nonrecursive, vbs, body) ->
      (vbs |>@ Vb.pat |>@@ free_unqualified_names_pat) @
      (vbs |>@ Vb.exp |>@@ recurse) @
      List.diff
        (recurse body)
        (vbs |>@@ Vb.names)
    | Pexp_let (Asttypes.Recursive, vbs, body) ->
      List.diff
        ((vbs |>@ Vb.pat |>@@ free_unqualified_names_pat) @ (vbs |>@ Vb.exp |>@@ recurse) @ recurse body)
        (vbs |>@@ Vb.names)
    | Pexp_function cases ->
      cases |>@@ free_unqualified_names_case
    | Pexp_fun (_, default, pat, body) ->
      free_unqualified_names_pat pat @
      (default |>& recurse ||& []) @
      List.diff (recurse body) (Pat.names pat)
    | Pexp_apply (e1, labeled_args) ->
      (e1 :: (labeled_args |>@ snd)) |>@@ recurse
    | Pexp_match (e, cases)
    | Pexp_try (e, cases) ->
      recurse e @ (cases |>@@ free_unqualified_names_case)
    | Pexp_array exps
    | Pexp_tuple exps ->
      exps |>@@ recurse
    | Pexp_construct (_, e_opt)
    | Pexp_variant (_, e_opt) ->
      e_opt |>& recurse ||& []
    | Pexp_record (fields, e_opt) ->
      (e_opt |>& recurse ||& []) @
      (fields |>@ snd |>@@ recurse)
    | Pexp_field (e, _) -> recurse e
    | Pexp_sequence (e1, e2)
    | Pexp_while (e1, e2)
    | Pexp_setfield (e1, _, e2) ->
      [e1; e2] |>@@ recurse
    | Pexp_ifthenelse (e1, e2, e3_opt) -> ([e1; e2] @ Option.to_list e3_opt) |>@@ recurse
    | Pexp_for (pat, e1, e2, _, body) ->
      free_unqualified_names_pat pat @
      ([e1; e2] |>@@ recurse) @
      List.diff (recurse body) (Pat.names pat)
    | Pexp_coerce (e, _, _)
    | Pexp_send (e, _)
    | Pexp_setinstvar (_, e)
    | Pexp_constraint (e, _)
    | Pexp_assert e
    | Pexp_lazy e
    | Pexp_poly (e, _)
    | Pexp_newtype (_, e)
    | Pexp_letexception (_, e) ->
      recurse e
    | Pexp_override overrides ->
      overrides |>@ snd |>@@ recurse
    | Pexp_letmodule (_, mod_exp, body) ->
      free_unqualified_names_mod mod_exp @ recurse body
    | Pexp_pack mod_exp ->
      free_unqualified_names_mod mod_exp
    | Pexp_object _ ->
      failwith "free_unqualified_names: classes not handled"
    | Pexp_open (_, _, _) ->
      failwith "free_unqualified_names: local opens not handled"
    end

and free_unqualified_names_mod { pmod_desc; _ } =
  let recurse = free_unqualified_names_mod in
  match pmod_desc with
  | Pmod_extension _
  | Pmod_ident _                 -> []
  | Pmod_structure struct_items  -> free_unqualified_names_struct_items struct_items
  | Pmod_unpack exp              -> free_unqualified_names exp
  | Pmod_constraint (mod_exp, _)
  | Pmod_functor (_, _, mod_exp) -> recurse mod_exp
  | Pmod_apply (m1, m2)          -> recurse m1 @ recurse m2

and free_unqualified_names_struct_items struct_items =
  let recurse = free_unqualified_names_struct_items in
  let recurse_exp = free_unqualified_names in
  match struct_items with
  | [] -> []
  | si::rest ->
    let later_names = recurse rest in
    begin match si.pstr_desc with
    | Pstr_eval (exp, _) ->
      free_unqualified_names exp @ later_names
    | Pstr_value (Asttypes.Nonrecursive, vbs) ->
      (vbs |>@ Vb.pat |>@@ free_unqualified_names_pat) @
      (vbs |>@ Vb.exp |>@@ recurse_exp) @
      List.diff
        later_names
        (vbs |>@@ Vb.names)
    | Pstr_value (Asttypes.Recursive, vbs) ->
      List.diff
        ((vbs |>@ Vb.pat |>@@ free_unqualified_names_pat) @ (vbs |>@ Vb.exp |>@@ recurse_exp) @ later_names)
        (vbs |>@@ Vb.names)
    | Pstr_primitive _
    | Pstr_type (_, _)
    | Pstr_typext _
    | Pstr_modtype _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension (_, _)
    | Pstr_exception _ ->
      later_names
    | Pstr_module { pmb_expr; _ } ->
      free_unqualified_names_mod pmb_expr @ later_names
    | Pstr_recmodule mod_bindings ->
      (mod_bindings |>@@ (fun { pmb_expr; _ } -> free_unqualified_names_mod pmb_expr)) @ later_names
    | Pstr_include _ ->
      failwith "free_unqualified_names_struct_items: includes not handled"
    | Pstr_open _ ->
      failwith "free_unqualified_names_struct_items: opens not handled"
    | Pstr_class _ ->
      failwith "free_unqualified_names_struct_items: classes not handled"
    end

and free_unqualified_names_pat pat =
  (* Any Ppat_open will make this wrong. Don't use them. *)
  pat
  |> Pat.flatten
  |>@@ fun pat -> names_in_vis_attrs pat.ppat_attributes

and names_in_vis_attrs attrs =
  Vis.all_from_attrs attrs
  |>@@ fun { exp } -> free_unqualified_names exp


(* Mapping is top-down, rather than bottom-up. *)
(* Using OCaml binding semantics, rather than Maniposynth's non-linear pseudosemantics. *)
(* handle_root_pat is only given the root pattern of a binding introduction (it's up to handle_root_pat to flatten&recurse, if need be) *)
let mapper_with_scope (init_scope_info : 'a) (handle_root_pat : 'a -> pattern -> 'a) (f : 'a -> expression -> expression) =
  let rec map_exp scope_info _ e =
    let e'                       = f scope_info e in
    let recurse                  = map_exp scope_info  (mapper scope_info) in
    let recurse'     scope_info' = map_exp scope_info' (mapper scope_info') in
    let map_children scope_info' = dflt_mapper.expr    (mapper scope_info') in
    let handle_case case =
      let scope_info' = handle_root_pat scope_info case.pc_lhs in
      let recurse' = recurse' scope_info' in
      case |> Case.map_guard recurse' |> Case.map_rhs recurse'
    in
    let ret desc = { e' with pexp_desc = desc } in
    begin match e'.pexp_desc with
    | Pexp_let (Asttypes.Nonrecursive, vbs, body)  -> let scope_info' = vbs |>@ Vb.pat |> List.fold_left handle_root_pat scope_info in ret @@ Pexp_let (Asttypes.Nonrecursive, vbs |>@ Vb.map_exp recurse, recurse' scope_info' body)
    | Pexp_let (Asttypes.Recursive, vbs, _)        -> let scope_info' = vbs |>@ Vb.pat |> List.fold_left handle_root_pat scope_info in map_children scope_info' e'
    | Pexp_match (scrutinee, cases)                -> ret @@ Pexp_match (recurse scrutinee, cases |>@ handle_case)
    | Pexp_try   (body, cases)                     -> ret @@ Pexp_try (recurse body, cases |>@ handle_case)
    | Pexp_function cases                          -> ret @@ Pexp_function (cases |>@ handle_case)
    | Pexp_fun (arg_label, default, pat, body)     -> let scope_info' = handle_root_pat scope_info pat in ret @@ Pexp_fun (arg_label, default |>& recurse, pat, recurse' scope_info' body)
    | Pexp_for (pat, e1, e2, dirflag, body)        -> let scope_info' = handle_root_pat scope_info pat in ret @@ Pexp_for (pat, recurse e1, recurse e2, dirflag, recurse' scope_info' body)
    | Pexp_letmodule (_str_loced, _mod_exp, _body) -> failwith "map_with_scope: letmodule not handled"
    | Pexp_pack _mod_exp                           -> failwith "map_with_scope: pack not handled"
    | Pexp_object _                                -> failwith "map_with_scope: classes not handled"
    | Pexp_open (_, _, _)                          -> failwith "map_with_scope: local opens not handled"
    | _                                            -> map_children scope_info e'
    end
  and map_struct_items scope_info _ sis =
    let map_si mapper' = dflt_mapper.structure_item mapper' in
    let sis'_rev, _ =
      sis
      |> List.fold_left begin fun (sis'_rev, scope_info) si ->
        (match si.pstr_desc with
        | Pstr_value (Asttypes.Nonrecursive, vbs) -> let scope_info' = vbs |>@ Vb.pat |> List.fold_left handle_root_pat scope_info in (map_si (mapper scope_info)  si :: sis'_rev, scope_info')
        | Pstr_value (Asttypes.Recursive, vbs)    -> let scope_info' = vbs |>@ Vb.pat |> List.fold_left handle_root_pat scope_info in (map_si (mapper scope_info') si :: sis'_rev, scope_info')
        | _                                       -> (map_si (mapper scope_info) si :: sis'_rev, scope_info)
        )
      end ([], scope_info)
    in
    List.rev sis'_rev
  and mapper scope_info = { dflt_mapper with expr = map_exp scope_info; structure = map_struct_items scope_info }
  in
  mapper init_scope_info

let map_exps_with_scope (init_scope_info : 'a) (handle_root_pat : 'a -> pattern -> 'a) (f : 'a -> expression -> expression) exp =
  let mapper = mapper_with_scope init_scope_info handle_root_pat f in
  mapper.expr mapper exp

let map_exps_with_scope_prog (init_scope_info : 'a) (handle_root_pat : 'a -> pattern -> 'a) (f : 'a -> expression -> expression) struct_items =
  let mapper = mapper_with_scope init_scope_info handle_root_pat f in
  mapper.structure mapper struct_items

(* Preserves old attrs and locs *)
(* Non-recursive *)
let apply_subst_on_exp subst exp =
  match exp.pexp_desc with
  | Pexp_ident ({ txt = Longident.Lident name; _ } as lid_loced) ->
    SMap.find_opt name subst
    |>& (fun name' -> { exp with pexp_desc = Pexp_ident {lid_loced with txt = Longident.Lident name'} })
    ||& exp
  | _ ->
    exp

(* Preserves old attrs and locs *)
let rename_unqualified_variables subst exp =
  let handle_root_pat subst pat = SMap.remove_all (Pat.names pat) subst in
  exp
  |> map_exps_with_scope subst handle_root_pat apply_subst_on_exp

(* Only handles single name pats for now, not as-pats. *)
(* Preserves old attrs and locs *)
let rename_pat_at pat_loc name' prog =
  let is_target_pat pat = Pat.is_single_name pat && Pat.loc pat = pat_loc in
  let handle_root_pat subst pat =
    let subst = SMap.remove_all (Pat.names pat) subst in
    match pat |> Pat.flatten |> List.find_opt is_target_pat with
    | Some pat -> SMap.add (Pat.single_name pat ||& "") name' subst
    | None     -> subst
  in
  prog
  |> map_exps_with_scope_prog SMap.empty handle_root_pat apply_subst_on_exp
  |> Pat.map_by is_target_pat (fun pat -> { pat with ppat_desc = (Pat.var name').ppat_desc })


exception Found_names of string list

(* Names in file only. Nearest name first (with the exception of as-pats, oh well). *)
let names_at exp_loc prog =
  let init_scope_info = [] in
  let handle_root_pat names pat = Pat.names pat @ names in
  let f names exp = if exp.pexp_loc = exp_loc then raise (Found_names names) else exp in
  try
    ignore @@ (map_exps_with_scope_prog init_scope_info handle_root_pat f prog);
    raise Not_found
  with Found_names names -> names
