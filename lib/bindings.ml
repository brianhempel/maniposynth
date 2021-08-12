(*

  Maniposynth offers non-linear editing, which means you, the
  programmer, should not have to worry so much about the order
  of bindings.

  In a perfect world, we could just throw all scope bindings in
  one bit letrec, but that does not work for a few reasons:

  1. OCaml ensures that side-effecting code runs top to bottom,
     so bare (non-lambda) computations cannot refer to other
     definitions in the letrec because OCaml will not attempt
     a dependency analysis to reorder the computatiosn.

  2. Only single variable patterns can be on the LHS of a
     letrec binding.

  We also want to support other binding movement scenarios,
  such as changing the scope of a binding.

*)

open Parsetree
open Shared.Ast
open Shared.Util

(*

  The non-linear playpens are:
  1. Top level
  2. Function bodies

  For each non-linear playpen, variable names should be unique. We look in the playpen
  for names that might be technically out of scope and then move them into scope for
  other uses within the playpen.

  Current limitations:
  A. letrecs and multi-lets are always moved together. But this is
     not much of a concern because Maniposynth does not generate non-rec multi-lets, and
     all bindings in a let-rec *should* be moved together.
  B. Multibindings (e.g. tuple patterns) are not broken up.
  C. Not concerned with constructor names, field labels, or moving modules around.
*)


(* Also searches in [@vis] attributes. *)
let rec free_unqualified_names exp =
  let recurse = free_unqualified_names in
  let free_unqualified_names_case { pc_lhs; pc_guard; pc_rhs } =
    List.diff
      (free_unqualified_names_pat pc_lhs @ (pc_guard |>& recurse ||& []) @ recurse pc_rhs)
      (Pat.names pc_lhs)
  in
  names_in_vis_attrs exp.pexp_attributes @
  match exp.pexp_desc with
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


(*
    Need two passes.

    Pass 1 moves existing items upward into scope.
    Pass 2 adds missing bindings.
*)

let rec extract_vb_group_with_name_top_level name struct_items =
  match struct_items with
  | []       -> None
  | si::rest ->
    begin match si.pstr_desc with
    | Pstr_value (recflag, vbs) when List.mem name (vbs |>@@ Vb.names) ->
      Some (recflag, vbs, rest)
    | _ ->
      begin match extract_vb_group_with_name_top_level name rest with
      | Some (recflag, vbs, rest') -> Some (recflag, vbs, si::rest')
      | None -> None
      end
    end

let rec extract_vb_group_with_name name body =
  let recurse = extract_vb_group_with_name name in
  match body.pexp_desc with
  | Pexp_let (recflag, vbs, body) when List.mem name (vbs |>@@ Vb.names)  -> Some (recflag, vbs, body)
  | Pexp_let (recflag, vbs, body)                                         -> recurse body |>& Tup3.map_thd (fun body' -> { body with pexp_desc = Pexp_let (recflag, vbs, body') })
  | Pexp_sequence (e1, e2) (* Treat Pexp_sequence as let () = e1 in e2 *) -> recurse e2   |>& Tup3.map_thd (fun e2'   -> { body with pexp_desc = Pexp_sequence (e1, e2') })
  | Pexp_letmodule (str_loced, mod_exp, body)                             -> recurse body |>& Tup3.map_thd (fun body' -> { body with pexp_desc = Pexp_letmodule (str_loced, mod_exp, body') })
  | _                                                                     -> None


let rec rearrange_struct_items defined_names struct_items =
  let open Asttypes in
  let recurse = rearrange_struct_items in
  let recurse_exp ?(defined_names' = defined_names) = rearrange_exp defined_names' in
  let recurse_mod ?(defined_names' = defined_names) = rearrange_mod defined_names' in
  match struct_items with
  | [] -> []
  | si::rest ->
    let rec fix_a_name_and_continue defined_names' si' names_needed =
      begin match names_needed with
      | []                -> si' :: recurse defined_names' rest
      | name::other_names ->
        begin match extract_vb_group_with_name_top_level name rest with
        | None                       -> fix_a_name_and_continue defined_names' si' other_names
        | Some (recflag, vbs, rest') -> recurse defined_names (StructItem.value recflag vbs :: si' :: rest')
        end
      end
    in
    begin match si.pstr_desc with
    | Pstr_eval (exp, attrs) ->
      let exp = recurse_exp exp in
      let si' = { si with pstr_desc = Pstr_eval (exp, attrs) } in
      let names_needed = List.diff (free_unqualified_names exp) defined_names in
      fix_a_name_and_continue defined_names si' names_needed
    | Pstr_value (Nonrecursive, vbs) ->
      let recflag', vbs', defined_names', names_needed = rearrange_nonrec_vbs defined_names vbs in
      let si' = { si with pstr_desc = Pstr_value (recflag', vbs') } in
      fix_a_name_and_continue defined_names' si' names_needed
    | Pstr_value (Recursive, vbs) ->
      let vbs', defined_names', names_needed = rearrange_rec_vbs defined_names vbs in
      let si' = { si with pstr_desc = Pstr_value (Recursive, vbs') } in
      fix_a_name_and_continue defined_names' si' names_needed
    | Pstr_module mod_binding ->
      let mod_binding' = { mod_binding with pmb_expr = recurse_mod mod_binding.pmb_expr } in
      let si' = { si with pstr_desc = Pstr_module mod_binding' } in
      let names_needed = List.diff (free_unqualified_names_mod mod_binding'.pmb_expr) defined_names in
      fix_a_name_and_continue defined_names si' names_needed
    | Pstr_recmodule mod_bindings ->
      let mod_bindings' = mod_bindings |>@ (fun mod_binding -> { mod_binding with pmb_expr = recurse_mod mod_binding.pmb_expr }) in
      let si' = { si with pstr_desc = Pstr_recmodule mod_bindings' } in
      let names_needed =
        List.diff
          (mod_bindings' |>@@ (fun mod_binding' -> free_unqualified_names_mod mod_binding'.pmb_expr))
          defined_names
      in
      fix_a_name_and_continue defined_names si' names_needed
    | Pstr_primitive _
    | Pstr_type (_, _)
    | Pstr_typext _
    | Pstr_exception _
    | Pstr_modtype _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension (_, _) ->
      si :: recurse defined_names rest
    | Pstr_include _ ->
      failwith "rearrange_struct_items: includes not handled"
    | Pstr_open _ ->
      failwith "rearrange_struct_items: opens not handled"
    | Pstr_class _ ->
      failwith "rearrange_struct_items: classes not handled"
    end

and rearrange_nonrec_vbs defined_names vbs =
  let vbs' = vbs |>@ Vb.map_exp (rearrange_exp defined_names) in
  let names_needed = List.diff (vbs' |>@ Vb.exp |>@@ free_unqualified_names) defined_names in
  (* If any of the needed names are defined here, make the binding recursive. *)
  let names_defined_here = vbs' |>@@ Vb.names in
  let names_defined_here_needed = List.inter names_defined_here names_needed in
  let recflag' = if List.any_overlap names_needed names_defined_here_needed then Asttypes.Recursive else Asttypes.Nonrecursive in
  let names_needed' = List.diff names_needed names_defined_here_needed in
  let defined_names' = names_defined_here @ defined_names in
  recflag', vbs', defined_names', names_needed'

and rearrange_rec_vbs defined_names vbs =
  let defined_names' = (vbs |>@@ Vb.names) @ defined_names in
  let vbs' = vbs |>@ Vb.map_exp (rearrange_exp defined_names') in
  let names_needed = List.diff (vbs' |>@ Vb.exp |>@@ free_unqualified_names) defined_names' in
  vbs', defined_names', names_needed

and rearrange_exp defined_names exp =
  let continue exp =
    let recurse ?(defined_names' = defined_names) = rearrange_exp defined_names' in
    let recurse_case defined_names { pc_lhs; pc_guard; pc_rhs } =
      let defined_names' = Pat.names pc_lhs @ defined_names in
      { pc_lhs = pc_lhs; pc_guard = pc_guard |>& recurse ~defined_names'; pc_rhs = recurse ~defined_names' pc_rhs }
    in
    (fun desc' -> { exp with pexp_desc = desc' }) @@
    begin match exp.pexp_desc with
    | Pexp_ident _
    | Pexp_new   _
    | Pexp_constant _
    | Pexp_extension _
    | Pexp_unreachable                          -> exp.pexp_desc
    | Pexp_let (recflag, vbs, body)             -> let defined_names' = (vbs |>@@ Vb.names) @ defined_names in Pexp_let (recflag, vbs, recurse ~defined_names' body)
    | Pexp_function cases                       -> Pexp_function (cases |>@ recurse_case defined_names)
    | Pexp_fun (arg_label, default, pat, body)  -> let defined_names' = Pat.names pat @ defined_names in Pexp_fun (arg_label, default |>& recurse, pat, recurse ~defined_names' body)
    | Pexp_apply (e1, labeled_args)             -> Pexp_apply (recurse e1, labeled_args |>@ Tup2.map_snd recurse)
    | Pexp_match (e, cases)                     -> Pexp_match (recurse e, cases |>@ recurse_case defined_names)
    | Pexp_try (e, cases)                       -> Pexp_try (recurse e, cases |>@ recurse_case defined_names)
    | Pexp_array exps                           -> Pexp_array (exps |>@ recurse)
    | Pexp_tuple exps                           -> Pexp_tuple (exps |>@ recurse)
    | Pexp_construct (lid_loced, e_opt)         -> Pexp_construct (lid_loced, e_opt |>& recurse)
    | Pexp_variant (str, e_opt)                 -> Pexp_variant (str, e_opt |>& recurse)
    | Pexp_record (fields, e_opt)               -> Pexp_record (fields |>@ Tup2.map_snd recurse, e_opt |>& recurse)
    | Pexp_field (e, lid_loced)                 -> Pexp_field (recurse e, lid_loced)
    | Pexp_sequence (e1, e2)                    -> Pexp_sequence (recurse e1, recurse e2)
    | Pexp_while (e1, e2)                       -> Pexp_while (recurse e1, recurse e2)
    | Pexp_setfield (e1, lid_loced, e2)         -> Pexp_setfield (recurse e1, lid_loced, recurse e2)
    | Pexp_ifthenelse (e1, e2, e3_opt)          -> Pexp_ifthenelse (recurse e1, recurse e2, e3_opt |>& recurse)
    | Pexp_for (pat, e1, e2, dirflag, body)     -> let defined_names' = Pat.names pat @ defined_names in Pexp_for (pat, recurse e1, recurse e2, dirflag, recurse ~defined_names' body)
    | Pexp_coerce (e, ct_opt, ct)               -> Pexp_coerce (recurse e, ct_opt, ct)
    | Pexp_send (e, str_loced)                  -> Pexp_send (recurse e, str_loced)
    | Pexp_setinstvar (str_loced, e)            -> Pexp_setinstvar (str_loced, recurse e)
    | Pexp_constraint (e, ct)                   -> Pexp_constraint (recurse e, ct)
    | Pexp_assert e                             -> Pexp_assert (recurse e)
    | Pexp_lazy e                               -> Pexp_lazy (recurse e)
    | Pexp_poly (e, ct_opt)                     -> Pexp_poly (recurse e, ct_opt)
    | Pexp_newtype (str_loced, e)               -> Pexp_newtype (str_loced, recurse e)
    | Pexp_letexception (exn_ctor, e)           -> Pexp_letexception (exn_ctor, recurse e)
    | Pexp_override overrides                   -> Pexp_override (overrides |>@ Tup2.map_snd recurse)
    | Pexp_letmodule (str_loced, mod_exp, body) -> Pexp_letmodule (str_loced, rearrange_mod defined_names mod_exp, recurse body)
    | Pexp_pack mod_exp                         -> Pexp_pack (rearrange_mod defined_names mod_exp)
    | Pexp_object _                             -> failwith "rearrange_exp: classes not handled"
    | Pexp_open (_, _, _)                       -> failwith "rearrange_exp: local opens not handled"
    end
  in
  let extract_a_name body names_needed =
    names_needed
    |> List.findmap_opt (fun name -> extract_vb_group_with_name name body)
  in
  let open Asttypes in
  match exp.pexp_desc with
  | Pexp_let (Nonrecursive, vbs, body) ->
    let recflag', vbs', _, names_needed = rearrange_nonrec_vbs defined_names vbs in
    begin match extract_a_name body names_needed with
    | None                               -> continue                     { exp with pexp_desc = Pexp_let (recflag', vbs', body) }
    | Some (new_recflag, new_vbs, body') -> Exp.let_ new_recflag new_vbs { exp with pexp_desc = Pexp_let (recflag', vbs', body') } |> rearrange_exp defined_names
    end
  | Pexp_let (Recursive, vbs, body) ->
    let vbs', _, names_needed = rearrange_rec_vbs defined_names vbs in
    begin match extract_a_name body names_needed with
    | None                               -> continue                     { exp with pexp_desc = Pexp_let (Recursive, vbs', body) }
    | Some (new_recflag, new_vbs, body') -> Exp.let_ new_recflag new_vbs { exp with pexp_desc = Pexp_let (Recursive, vbs', body') } |> rearrange_exp defined_names
    end
  (* Treat Pexp_sequence as let () = e1 in e2 *)
  | Pexp_sequence (e1, e2) ->
    let e1' = rearrange_exp defined_names e1 in
    let names_needed = List.diff (free_unqualified_names e1') defined_names in
    begin match extract_a_name e2 names_needed with
    | None                             -> continue                     { exp with pexp_desc = Pexp_sequence (e1', e2) }
    | Some (new_recflag, new_vbs, e2') -> Exp.let_ new_recflag new_vbs { exp with pexp_desc = Pexp_sequence (e1', e2') } |> rearrange_exp defined_names
    end
  | Pexp_letmodule (str_loced, mod_exp, body) ->
    let mod_exp' = rearrange_mod defined_names mod_exp in
    let names_needed = List.diff (free_unqualified_names_mod mod_exp') defined_names in
    begin match extract_a_name body names_needed with
    | None                               -> continue                     { exp with pexp_desc = Pexp_letmodule (str_loced, mod_exp', body) }
    | Some (new_recflag, new_vbs, body') -> Exp.let_ new_recflag new_vbs { exp with pexp_desc = Pexp_letmodule (str_loced, mod_exp', body') } |> rearrange_exp defined_names
    end
  | _ ->
    continue exp

and rearrange_mod defined_names modl =
  let recurse = rearrange_mod defined_names in
  match modl.pmod_desc with
  | Pmod_extension _
  | Pmod_ident _                               -> modl
  | Pmod_structure struct_items                -> { modl with pmod_desc = Pmod_structure (rearrange_struct_items defined_names struct_items) }
  | Pmod_unpack exp                            -> { modl with pmod_desc = Pmod_unpack (rearrange_exp defined_names exp) }
  | Pmod_constraint (mod_exp, mod_type)        -> { modl with pmod_desc = Pmod_constraint (recurse mod_exp, mod_type) }
  | Pmod_functor (name, mod_type_opt, mod_exp) -> { modl with pmod_desc = Pmod_functor (name, mod_type_opt, recurse mod_exp) }
  | Pmod_apply (m1, m2)                        -> { modl with pmod_desc = Pmod_apply (recurse m1, recurse m2) }



(* Only add a missing binding to the top level if the name is used in multiple top level bindings. *)
(* Otherwise, add just inside the top level binding where the name is needed. *)
let rec add_missing_bindings_struct_items defined_names struct_items =
  let open Asttypes in
  let recurse = add_missing_bindings_struct_items in
  let recurse_exp = add_missing_bindings_exp in
  let recurse_mod = add_missing_bindings_mod in
  match struct_items with
  | [] -> []
  | si::rest ->
    let add_bindings_and_continue ~names_for_si ~names_after_si ~names_free_si_rhs ~make_si_desc' =
      let names_needed_si             = List.diff names_free_si_rhs names_for_si in
      let names_needed_remaining_prog = List.diff (free_unqualified_names_struct_items rest) names_after_si in
      let names_to_define_here        = List.inter names_needed_si names_needed_remaining_prog |> List.dedup in
      let new_sis                     = names_to_define_here |>@ (fun name -> StructItem.value Nonrecursive [Vb.mk (Pat.var name) Exp.hole]) in
      let si'                         = { si with pstr_desc = make_si_desc' (names_to_define_here @ names_for_si) } in
      new_sis @ [si'] @ recurse (names_to_define_here @ names_after_si) rest
    in
    begin match si.pstr_desc with
    | Pstr_eval (exp, attrs) ->
      add_bindings_and_continue
        ~names_for_si:defined_names
        ~names_after_si:defined_names
        ~names_free_si_rhs:(free_unqualified_names exp)
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_eval (recurse_exp names_for_si' exp, attrs)
        end
    | Pstr_value (Nonrecursive, vbs) ->
      add_bindings_and_continue
        ~names_for_si:defined_names
        ~names_after_si:((vbs |>@@ Vb.names) @ defined_names)
        ~names_free_si_rhs:(vbs |>@ Vb.exp |>@@ free_unqualified_names)
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_value (Nonrecursive, vbs |>@ Vb.map_exp (recurse_exp names_for_si'))
        end
    | Pstr_value (Recursive, vbs) ->
      let defined_names' = (vbs |>@@ Vb.names) @ defined_names in
      add_bindings_and_continue
        ~names_for_si:defined_names'
        ~names_after_si:defined_names'
        ~names_free_si_rhs:(vbs |>@ Vb.exp |>@@ free_unqualified_names)
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_value (Recursive, vbs |>@ Vb.map_exp (recurse_exp names_for_si'))
        end
    | Pstr_module mod_binding ->
      add_bindings_and_continue
        ~names_for_si:defined_names
        ~names_after_si:defined_names
        ~names_free_si_rhs:(free_unqualified_names_mod mod_binding.pmb_expr)
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_module { mod_binding with pmb_expr = recurse_mod names_for_si' mod_binding.pmb_expr }
        end
    | Pstr_recmodule mod_bindings ->
      add_bindings_and_continue
        ~names_for_si:defined_names
        ~names_after_si:defined_names
        ~names_free_si_rhs:(mod_bindings |>@@ (fun { pmb_expr; _ } -> free_unqualified_names_mod pmb_expr))
        ~make_si_desc':begin fun names_for_si' ->
          let mod_bindings' = mod_bindings |>@ (fun mod_binding -> { mod_binding with pmb_expr = recurse_mod names_for_si' mod_binding.pmb_expr }) in
          Pstr_recmodule mod_bindings'
        end
    | Pstr_primitive _
    | Pstr_type (_, _)
    | Pstr_typext _
    | Pstr_exception _
    | Pstr_modtype _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension (_, _) ->
        si :: recurse defined_names rest
    | Pstr_include _ ->
      failwith "rearrange_struct_items: includes not handled"
    | Pstr_open _ ->
      failwith "rearrange_struct_items: opens not handled"
    | Pstr_class _ ->
      failwith "rearrange_struct_items: classes not handled"
    end

(* Add as soon as possible, but not right outside a lambda. *)
and add_missing_bindings_exp defined_names exp =
  match exp.pexp_desc with
  | Pexp_fun (arg_label, default, pat, body) ->
    { exp with pexp_desc = Pexp_fun (arg_label, default, pat, add_missing_bindings_exp (Pat.names pat @ defined_names) body) }
  | _ ->
    let names_needed = List.diff (free_unqualified_names exp) defined_names |> List.dedup in
    List.fold_right
      (fun name body -> Exp.let_ Asttypes.Nonrecursive [Vb.mk (Pat.var name) Exp.hole] body)
      names_needed
      exp

 and add_missing_bindings_mod defined_names modl =
  let recurse = add_missing_bindings_mod defined_names in
  match modl.pmod_desc with
  | Pmod_extension _
  | Pmod_ident _                               -> modl
  | Pmod_structure struct_items                -> { modl with pmod_desc = Pmod_structure (add_missing_bindings_struct_items defined_names struct_items) }
  | Pmod_unpack exp                            -> { modl with pmod_desc = Pmod_unpack (add_missing_bindings_exp defined_names exp) }
  | Pmod_constraint (mod_exp, mod_type)        -> { modl with pmod_desc = Pmod_constraint (recurse mod_exp, mod_type) }
  | Pmod_functor (name, mod_type_opt, mod_exp) -> { modl with pmod_desc = Pmod_functor (name, mod_type_opt, recurse mod_exp) }
  | Pmod_apply (m1, m2)                        -> { modl with pmod_desc = Pmod_apply (recurse m1, recurse m2) }



(* Naive extraction produces e.g. `f (match x with y -> y)` *)
(* Turn that into `match x with y -> f y` *)
let move_matches_outside prog =
  let rec move exp =
    let ret match_exp scrutinee cases make_branch_desc =
      let cases' = cases |>@ Case.map_rhs (fun branch -> move { exp with pexp_desc = make_branch_desc branch }) in
      { match_exp with pexp_desc = Pexp_match (scrutinee, cases') }
    in
    match exp.pexp_desc with
    (* let x = match y with p -> e1 in e2 *)
    (* Single case in match means means match was just inserted and should be moved. *)
    | Pexp_let (recflag, [{ pvb_expr = { pexp_desc = Pexp_match (scrutinee, ([_] as cases)); _ } as match_exp; _} as vb], body) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_let (recflag, [{ vb with pvb_expr = branch }], body))
    (* match in function position *)
    | Pexp_apply ({ pexp_desc = Pexp_match (scrutinee, cases); _ } as match_exp, args) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_apply (branch, args))
    (* match in an arg position *)
    | Pexp_apply (fexp, args) ->
      args
      |> List.extractmap_opt begin fun (arg_label, arg_exp) ->
        begin match arg_exp.pexp_desc with
        | Pexp_match (scrutinee, cases) -> Some (arg_label, arg_exp, scrutinee, cases)
        | _                             -> None
        end
      end
      |>& begin fun ((arg_label, match_exp, scrutinee, cases), remake_args) ->
        ret match_exp scrutinee cases (fun branch -> Pexp_apply (fexp, remake_args [(arg_label, branch)]))
      end
      ||& exp
    (* match in scrutinee postion...this is common because it's how we represent subvalue extractions in the HTML *)
    | Pexp_match ({ pexp_desc = Pexp_match (scrutinee, ([_] as cases)); _ } as match_exp, cases2) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_match (branch, cases2))
    | Pexp_tuple elems ->
      elems
      |> List.extractmap_opt begin fun elem ->
        begin match elem.pexp_desc with
        | Pexp_match (scrutinee, cases) -> Some (elem, scrutinee, cases)
        | _ -> None
        end
      end
      |>& begin fun ((match_exp, scrutinee, cases), remake_elems) ->
        ret match_exp scrutinee cases (fun branch -> Pexp_tuple (remake_elems [branch]))
      end
      ||& exp
    | Pexp_array elems ->
      elems
      |> List.extractmap_opt begin fun elem ->
        begin match elem.pexp_desc with
        | Pexp_match (scrutinee, cases) -> Some (elem, scrutinee, cases)
        | _ -> None
        end
      end
      |>& begin fun ((match_exp, scrutinee, cases), remake_elems) ->
        ret match_exp scrutinee cases (fun branch -> Pexp_array (remake_elems [branch]))
      end
      ||& exp
    | Pexp_construct (lid_loced, Some ({ pexp_desc = Pexp_match (scrutinee, cases); _ } as match_exp)) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_construct (lid_loced, Some branch))
    | Pexp_variant (str, Some ({ pexp_desc = Pexp_match (scrutinee, cases); _ } as match_exp)) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_variant (str, Some branch))
    (* in base position *)
    | Pexp_record (fields, Some ({ pexp_desc = Pexp_match (scrutinee, cases); _ } as match_exp)) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_record (fields, Some branch))
    (* in field position *)
    | Pexp_record (fields, base_opt) ->
      fields
      |> List.extractmap_opt begin fun (lid_loced, field_exp) ->
        begin match field_exp.pexp_desc with
        | Pexp_match (scrutinee, cases) -> Some (lid_loced, field_exp, scrutinee, cases)
        | _                             -> None
        end
      end
      |>& begin fun ((lid_loced, match_exp, scrutinee, cases), remake_fields) ->
        ret match_exp scrutinee cases (fun branch -> Pexp_record (remake_fields [(lid_loced, branch)], base_opt))
      end
      ||& exp
    | Pexp_field ({ pexp_desc = Pexp_match (scrutinee, cases); _ } as match_exp, lid_loced) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_field (branch, lid_loced))
    (* on lhs *)
    | Pexp_setfield ({ pexp_desc = Pexp_match (scrutinee, cases); _ } as match_exp, lid_loced, rhs) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_setfield (branch, lid_loced, rhs))
    (* on rhs *)
    | Pexp_setfield (lhs, lid_loced, ({ pexp_desc = Pexp_match (scrutinee, cases); _ } as match_exp)) ->
      ret match_exp scrutinee cases (fun branch -> Pexp_setfield (lhs, lid_loced, branch))
    | _ -> exp
  in
  prog
  |> Exp.map move

(* Need final tenv to know what constructors exist *)
let add_missing_cases final_tenv prog =
  let avoid_names = StructItems.deep_names prog in
  (* At this point, the program may not type b/c of missing bindings or missing cases. *)
  (* So, best effort. *)
  prog
  |> Exp.map begin fun exp ->
    match exp.pexp_desc with
    (* first pattern is a ctor *)
    | Pexp_match (scrutinee, (({ pc_lhs = { ppat_desc = Ppat_construct ({ txt = Longident.Lident ctor_name; _ }, _); _}; _}::_) as existing_cases)) ->
      let all_ctor_cases = Case_gen.gen_ctor_cases_from_ctor_name ~avoid_names ctor_name final_tenv in
      (* Conservative, may generate unreachable cases. *)
      let needed_cases =
        (* Is there a catchall? *)
        if List.exists (fun case -> Pat.is_catchall case.pc_lhs && case.pc_guard = None) existing_cases then [] else
        all_ctor_cases
        |>@? begin fun new_case ->
          (* Keep cases that do not appear in existing_cases *)
          match Pat.ctor_lid_loced new_case.pc_lhs with
          | Some { txt = ctor_lid; _ } ->
            not @@ List.exists begin fun existing_case ->
              existing_case.pc_guard = None &&
              match existing_case.pc_lhs.ppat_desc with
              (* C         *)
              | Ppat_construct ({ txt = ctor_lid'; _}, None)                                    when ctor_lid = ctor_lid'                                      -> true
              (* C x       *)
              | Ppat_construct ({ txt = ctor_lid'; _}, Some pat)                                when ctor_lid = ctor_lid' && Pat.is_catchall pat               -> true
              (* C (x,y,z) *)
              | Ppat_construct ({ txt = ctor_lid'; _}, Some { ppat_desc = Ppat_tuple pats; _ }) when ctor_lid = ctor_lid' && List.for_all Pat.is_catchall pats -> true
              | _                                                                                                                                              -> false
            end existing_cases
          | None -> failwith "unreachable"
        end
      in
      { exp with pexp_desc = Pexp_match (scrutinee, existing_cases @ needed_cases) }
    | _ ->
      exp
  end

let fixup_matches final_tenv prog =
  prog
  |> move_matches_outside
  |> add_missing_cases final_tenv
  (* |> consolidate_cases *)

(* Need final tenv to know what constructors exist *)
let fixup final_tenv prog =
  let defined_names = SSet.elements Name.pervasives_names in
  prog
  |> fixup_matches final_tenv
  |> rearrange_struct_items defined_names
  |> add_missing_bindings_struct_items defined_names





(* Pats_in_scope_* assumes a fixup happens. *)

(* exception Found of pattern list *)

(* Does *not* include patterns outside the program *)
(* let rec pats_in_scope_struct loc pats struct_items =
  let pats =
    (struct_items |>@& StructItem.vbs_opt |> List.concat |>@ Vb.pat |>@@ Pat.flatten)
    @ pats
  in
  struct_items |> List.iter begin fun si ->
    if si.pstr_loc = loc then raise (Found pats) else
    match si.pstr_desc with
    | Pstr_eval (exp, _)          -> pats_in_scope_exp loc pats exp
    | Pstr_value (_, vbs)         -> pats_in_scope_vbs loc pats vbs
    | Pstr_module mod_binding     -> pats_in_scope_mod loc pats mod_binding.pmb_expr
    | Pstr_recmodule mod_bindings -> mod_bindings |> List.iter (fun { pmb_expr; _ } -> pats_in_scope_mod loc pats pmb_expr)
    | Pstr_primitive _
    | Pstr_type (_, _)
    | Pstr_typext _
    | Pstr_exception _
    | Pstr_modtype _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension (_, _) -> ()
    | Pstr_include _ ->
      failwith "rearrange_struct_items: includes not handled"
    | Pstr_open _ ->
      failwith "rearrange_struct_items: opens not handled"
    | Pstr_class _ ->
      failwith "rearrange_struct_items: classes not handled"
  end

and pats_in_scope_exp loc pats exp =
  if exp.pexp_loc = loc then raise (Found pats) else
  let recurse = pats_in_scope_exp loc in
  let pats_in_scope_case { pc_lhs; pc_guard; pc_rhs } =
    let pats = Pat.flatten pc_lhs @ pats in
    Option.iter (recurse pats) pc_guard;
    recurse pats pc_rhs
  in
  match exp.pexp_desc with
  | Pexp_function cases -> (* don't plan to handle rearranging function cases *)
    List.iter pats_in_scope_case cases
  | Pexp_fun (_, default, pat, body) ->
    Option.iter (recurse pats) default;
    recurse (Pat.flatten pat @ pats) body
  | Pexp_try (e, cases) -> (* don't plan to handle rearranging try cases *)
    recurse pats e;
    List.iter pats_in_scope_case cases
  | _ ->
    let rec gather_vbs exp = (* Only for testing their locs *)
      match exp.pexp_desc with
      | Pexp_let (_, vbs, e)     -> vbs @ gather_vbs e
      | Pexp_sequence (_, e2)    -> gather_vbs e2
      | Pexp_match (_, cases)    -> cases |>@ Case.rhs |>@@ gather_vbs
      | Pexp_letmodule (_, _, e) -> gather_vbs e
      | _                        -> []
    in
    let rec gather_pats exp =
      match exp.pexp_desc with
      | Pexp_let (_, vbs, e)     -> (vbs |>@ Vb.pat |>@@ Pat.flatten) @ gather_pats e
      | Pexp_sequence (_, e2)    -> gather_pats e2
      | Pexp_match (_, cases)    -> (cases |>@ Case.lhs |>@@ Pat.flatten) @ (cases |>@ Case.rhs |>@@ gather_pats)
      | Pexp_letmodule (_, _, e) -> gather_pats e
      | _                        -> []
    in
    let rec intermediate_exps exp = (* A chunk of the trunk of our walk *)
      match exp.pexp_desc with
      | Pexp_let (_, _, e)       -> exp :: intermediate_exps e
      | Pexp_sequence (_, e2)    -> exp :: intermediate_exps e2
      | Pexp_match (_, cases)    -> exp :: (cases |>@ Case.rhs |>@@ intermediate_exps)
      | Pexp_letmodule (_, _, e) -> exp :: intermediate_exps e
      | _                        -> [exp]
    in
    let rec next_exps exp = (* Where to go after the chunk of the trunk *)
      match exp.pexp_desc with
      | Pexp_let (_, vbs, e)     -> (vbs |>@ Vb.exp) @ next_exps e
      | Pexp_sequence (e1, e2)   -> e1 :: next_exps e2
      | Pexp_match (e, cases)    -> e :: (cases |>@& Case.guard_opt) @ (cases |>@ Case.rhs |>@@ next_exps)
      | Pexp_letmodule (_, _, e) -> next_exps e
      | _                        -> Exp.child_exps exp
    in
    let pats = gather_pats exp @ pats in
    gather_vbs exp |> List.iter begin fun vb ->
      if vb.pvb_loc = loc then raise (Found pats)
    end;
    intermediate_exps exp |> List.iter begin fun exp ->  (* Will include this exp. *)
      if exp.pexp_loc = loc then raise (Found pats)
    end;
    next_exps exp |> List.iter (recurse pats)

and pats_in_scope_vbs loc pats vbs = (* pats already includes all other vbs at this level *)
  vbs |> List.iter begin fun vb ->
    if vb.pvb_loc = loc then raise (Found pats)
  end;
  vbs |>@ Vb.exp |> List.iter (pats_in_scope_exp loc pats)

and pats_in_scope_mod loc pats modl =
  match modl.pmod_desc with
  | Pmod_extension _
  | Pmod_ident _                                 -> ()
  | Pmod_structure struct_items                  -> pats_in_scope_struct loc pats struct_items
  | Pmod_unpack exp                              -> pats_in_scope_exp loc pats exp
  | Pmod_constraint (mod_exp, _mod_type)         -> pats_in_scope_mod loc pats mod_exp
  | Pmod_functor (_name, _mod_type_opt, mod_exp) -> pats_in_scope_mod loc pats mod_exp
  | Pmod_apply (m1, m2)                          -> pats_in_scope_mod loc pats m1; pats_in_scope_mod loc pats m2
 *)


(* Checks locs of struct_items, vbs, and exps. (Not pats). *)
(* let pats_in_scope_at loc prog =
  try pats_in_scope_struct loc [] prog; failwith @@ "pats_in_scope_at: Could not find loc " ^ Loc.to_string loc
  with Found pats -> pats *)


(* let _ =
  let prog = StructItems.from_string "let x = y\nlet y = 10\nlet z = length" in
  fixup prog |> StructItems.to_string |> print_endline *)
