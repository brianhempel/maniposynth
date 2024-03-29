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
open Scope

(*

  The non-linear playpens are:
  1. Structures (including top-level)
  2. Value-binding RHS
  3. Function bodies

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


type rearrangment_root (* non-linear playpen; something rendered as a canvas holding TVs *)
  = RR_StructItems of structure
  | RR_Exp of expression


exception Rearrangment_roots_found of rearrangment_root list

(* For finding what names could be in scope at a hole, were a fixup to occur. *)
(* Most deeply nested roots are first in the returned list, top-level is last. *)
(* Should work the same as maniposynth.js vbsHolderForInsert for all practial purposes (which finds first self or ancenstor .exp.fun or .vbs). *)
(* And the places where View.local_canvas_vbs_and_returns_htmls is called. *)
let rec rearrangement_roots_at ?(higher_roots = []) exp_loc prog =
  try
    struct_rearrangement_roots_at ~higher_roots exp_loc prog;
    []
  with Rearrangment_roots_found roots ->
    roots

and struct_rearrangement_roots_at ?(higher_roots = []) exp_loc struct_items =
  struct_items
  |> List.iter begin fun si ->
    match si.pstr_desc with
    | Pstr_eval (exp, _attrs) ->
      exp_rearrangement_roots_at ~higher_roots:(RR_StructItems struct_items :: higher_roots) exp_loc exp
    | Pstr_value (_, vbs) ->
      vbs |>@ Vb.exp |> List.iter begin fun rhs ->
        exp_rearrangement_roots_at ~higher_roots:(RR_Exp rhs :: RR_StructItems struct_items :: higher_roots) exp_loc rhs
      end
    | Pstr_module mod_binding ->
      mod_rearrangement_roots_at ~higher_roots:(RR_StructItems struct_items :: higher_roots) exp_loc mod_binding.pmb_expr
    | Pstr_recmodule mod_bindings ->
      mod_bindings |> List.iter begin fun mb ->
        mod_rearrangement_roots_at ~higher_roots:(RR_StructItems struct_items :: higher_roots) exp_loc mb.pmb_expr
      end
    | Pstr_primitive _
    | Pstr_type (_, _)
    | Pstr_typext _
    | Pstr_exception _
    | Pstr_modtype _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension (_, _) ->
      ()
    | Pstr_include _ ->
      failwith "rearrange_struct_items: includes not handled"
    | Pstr_open _ ->
      failwith "rearrange_struct_items: opens not handled"
    | Pstr_class _ ->
      failwith "rearrange_struct_items: classes not handled"
  end

and exp_rearrangement_roots_at ?(higher_roots = []) exp_loc exp =
  if exp.pexp_loc = exp_loc then raise (Rearrangment_roots_found higher_roots) else
  begin
    begin match exp.pexp_desc with
    | Pexp_let (_, vbs, _)           ->
      vbs |>@ Vb.exp |> List.iter begin fun rhs ->
        exp_rearrangement_roots_at ~higher_roots:(RR_Exp rhs :: higher_roots) exp_loc rhs
      end
    | Pexp_function _                -> ()
    | Pexp_fun (_, _, _, body)       -> if Exp.is_fun body then () else exp_rearrangement_roots_at ~higher_roots:(RR_Exp body :: higher_roots) exp_loc body
    | Pexp_letmodule (_, mod_exp, _) -> mod_rearrangement_roots_at ~higher_roots exp_loc mod_exp
    | Pexp_pack mod_exp              -> mod_rearrangement_roots_at ~higher_roots exp_loc mod_exp
    | Pexp_object _                  -> failwith "exp_rearrangement_roots_at: classes not handled"
    | Pexp_open (_, _, _)            -> failwith "exp_rearrangement_roots_at: local opens not handled"
    | _                              -> ()
    end;
    Exp.child_exps exp
    |> List.iter (exp_rearrangement_roots_at ~higher_roots exp_loc)
  end

and mod_rearrangement_roots_at ?(higher_roots = []) exp_loc modl =
  let recurse = mod_rearrangement_roots_at ~higher_roots exp_loc in
  match modl.pmod_desc with
  | Pmod_extension _
  | Pmod_ident _                                 -> ()
  | Pmod_structure struct_items                  -> struct_rearrangement_roots_at ~higher_roots exp_loc struct_items
  | Pmod_unpack exp                              -> exp_rearrangement_roots_at ~higher_roots exp_loc exp
  | Pmod_constraint (mod_exp, _mod_type)         -> recurse mod_exp
  | Pmod_functor (_name, _mod_type_opt, mod_exp) -> recurse mod_exp
  | Pmod_apply (m1, m2)                          -> recurse m1; recurse m2

let rec terminal_exps exp = (* Dual of gather_vbs *)
  match exp.pexp_desc with
  | Pexp_let (_, _, e)       -> terminal_exps e
  | Pexp_sequence (_, e2)    -> terminal_exps e2
  | Pexp_match (_, cases)    -> cases |>@ Case.rhs |>@@ terminal_exps
  | Pexp_letmodule (_, _, e) -> terminal_exps e
  | Pexp_constraint (e, _)   -> terminal_exps e
  | _                        -> [exp]

(* should cohere with extract_vb_group_with_name *)
let rec movable_names_exp ?(names = []) exp =
  let recurse ?(names = names) exp = movable_names_exp ~names exp in
  match exp.pexp_desc with
  | Pexp_let (_, vbs, e)        -> recurse ~names:((vbs |>@@ Vb.names) @ names) e
  | Pexp_sequence (_, e2)       -> recurse e2
  | Pexp_letmodule (_, _, body) -> recurse body
  | _                           -> names



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
  | Pexp_let (recflag, vbs, body) when List.mem name (vbs |>@@ Vb.names)  -> Some (recflag, vbs, body, name)
  | Pexp_let (recflag, vbs, body)                                         -> recurse body |>& Tup4.map_thd (fun body' -> { body with pexp_desc = Pexp_let (recflag, vbs, body') })
  | Pexp_sequence (e1, e2) (* Treat Pexp_sequence as let () = e1 in e2 *) -> recurse e2   |>& Tup4.map_thd (fun e2'   -> { body with pexp_desc = Pexp_sequence (e1, e2') })
  | Pexp_letmodule (str_loced, mod_exp, body)                             -> recurse body |>& Tup4.map_thd (fun body' -> { body with pexp_desc = Pexp_letmodule (str_loced, mod_exp, body') })
  | _                                                                     -> None

let move_type_decls_to_top struct_items =
  let top_sis, rest_sis =
    struct_items
    |> List.partition begin function { pstr_desc; _ } ->
      match pstr_desc with
      | Pstr_eval (_, _)      -> false
      | Pstr_value (_, _)     -> false
      | Pstr_extension (_, _) -> false
      | _                     -> true
    end
  in
  top_sis @ rest_sis

let rec rearrange_struct_items struct_items =
  let movable_names = StructItems.names struct_items in
  rearrange_struct_items' movable_names struct_items

and rearrange_struct_items' ?(names_already_moved_here = []) later_movable_names struct_items =
  let recurse = rearrange_struct_items' in
  let recurse_exp = rearrange_exp in
  let recurse_mod = rearrange_mod in
  match struct_items with
  | [] -> []
  | si::rest ->
    let rec fix_a_name_and_continue later_movable_names' si' names_needed =
      begin match names_needed with
      | []                -> si' :: recurse later_movable_names' rest
      | name::other_names ->
        begin match extract_vb_group_with_name_top_level name rest with
        | None                       -> fix_a_name_and_continue later_movable_names' si' other_names
        | Some (recflag, vbs, rest') ->
          (* Cycle check. *)
          if List.mem name names_already_moved_here
          then fix_a_name_and_continue later_movable_names' si' other_names
          else recurse ~names_already_moved_here:(name::names_already_moved_here) later_movable_names (StructItem.value recflag vbs :: si' :: rest')
        end
      end
    in
    begin match si.pstr_desc with
    | Pstr_eval (exp, attrs) ->
      let exp = recurse_exp exp in
      let si' = { si with pstr_desc = Pstr_eval (exp, attrs) } in
      let names_needed = List.inter (free_unqualified_names exp) later_movable_names in
      fix_a_name_and_continue later_movable_names si' names_needed
    | Pstr_value (recflag, vbs) ->
      let later_movable_names', recflag', vbs', names_needed = rearrange_vbs later_movable_names recflag vbs in
      let si' = { si with pstr_desc = Pstr_value (recflag', vbs') } in
      fix_a_name_and_continue later_movable_names' si' names_needed
    | Pstr_module mod_binding ->
      let mod_binding' = { mod_binding with pmb_expr = recurse_mod mod_binding.pmb_expr } in
      let si' = { si with pstr_desc = Pstr_module mod_binding' } in
      let names_needed = List.inter (free_unqualified_names_mod mod_binding'.pmb_expr) later_movable_names in
      fix_a_name_and_continue later_movable_names si' names_needed
    | Pstr_recmodule mod_bindings ->
      let mod_bindings' = mod_bindings |>@ (fun mod_binding -> { mod_binding with pmb_expr = recurse_mod mod_binding.pmb_expr }) in
      let si' = { si with pstr_desc = Pstr_recmodule mod_bindings' } in
      let names_needed =
        List.inter
          (mod_bindings' |>@@ (fun mod_binding' -> free_unqualified_names_mod mod_binding'.pmb_expr))
          later_movable_names
      in
      fix_a_name_and_continue later_movable_names si' names_needed
    | Pstr_primitive _
    | Pstr_type (_, _)
    | Pstr_typext _
    | Pstr_exception _
    | Pstr_modtype _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension (_, _) ->
      si :: recurse later_movable_names rest
    | Pstr_include _ ->
      failwith "rearrange_struct_items: includes not handled"
    | Pstr_open _ ->
      failwith "rearrange_struct_items: opens not handled"
    | Pstr_class _ ->
      failwith "rearrange_struct_items: classes not handled"
    end

and rearrange_vbs later_movable_names recflag vbs =
  let vbs' = vbs |>@ Vb.map_exp rearrange_exp in
  let names_defined_here = vbs' |>@@ Vb.names in
  let names_needed = List.inter (vbs' |>@ Vb.exp |>@@ free_unqualified_names) later_movable_names (* This includes the names in vbs *) in
  let names_defined_here_needed = List.inter names_defined_here names_needed in
  (* If any of the needed names are defined here, make the binding recursive. *)
  let recflag' = if recflag = Asttypes.Nonrecursive && List.any_overlap names_needed names_defined_here_needed then Asttypes.Recursive else recflag in
  (* let si' = { si with pstr_desc = Pstr_value (recflag', vbs') } in *)
  let names_needed' = List.diff names_needed names_defined_here_needed in
  let later_movable_names' = List.diff later_movable_names names_defined_here in
  (later_movable_names', recflag', vbs', names_needed')
  (* fix_a_name_and_continue later_movable_names' si' names_needed' *)

and rearrange_exp exp =
  let movable_names = movable_names_exp exp in
  (* print_endline (movable_names |> String.concat ", ");
  print_endline (Exp.to_string exp); *)
  rearrange_exp' movable_names exp

and rearrange_exp' ?(names_already_moved_here = []) later_movable_names exp =
  let recurse = rearrange_exp' in
  (* let continue exp =
    (fun desc' -> { exp with pexp_desc = desc' }) @@
    begin match exp.pexp_desc with
    | Pexp_let (recflag, vbs, body)             -> let later_movable_names' = List.diff later_movable_names (vbs |>@@ Vb.names) in Pexp_let (recflag, vbs, recurse later_movable_names' body)
    | Pexp_sequence (e1, e2)                    -> Pexp_sequence (e1, recurse later_movable_names e2)
    | Pexp_letmodule (str_loced, mod_exp, body) -> Pexp_letmodule (str_loced, mod_exp, recurse later_movable_names body)
    end
  in *)
  let extract_a_name body names_needed =
    List.diff names_needed names_already_moved_here (* Avoid cycles. *)
    |> List.findmap_opt (fun name -> extract_vb_group_with_name name body)
  in
  let recurse_case { pc_lhs; pc_guard; pc_rhs } =
    { pc_lhs = pc_lhs; pc_guard = pc_guard |>& rearrange_exp; pc_rhs = rearrange_exp pc_rhs }
  in
  let rewrap desc' = { exp with pexp_desc = desc' } in
  let wrap_with_let_and_continue new_recflag new_vbs name desc' =
    Exp.let_ new_recflag new_vbs { exp with pexp_desc = desc' }
    |> recurse ~names_already_moved_here:(name::names_already_moved_here) later_movable_names
  in
  match exp.pexp_desc with
  | Pexp_let (recflag, vbs, body) ->
    let later_movable_names', recflag', vbs', names_needed = rearrange_vbs later_movable_names recflag vbs in
    begin match extract_a_name body names_needed with
    | None                                     -> Pexp_let (recflag', vbs', rearrange_exp' later_movable_names' body) |> rewrap
    | Some (new_recflag, new_vbs, body', name) -> Pexp_let (recflag', vbs', body') |> wrap_with_let_and_continue new_recflag new_vbs name
    end
  (* Treat Pexp_sequence as let () = e1 in e2 *)
  | Pexp_sequence (e1, e2) ->
    let e1' = recurse later_movable_names e1 in
    let names_needed = List.inter (free_unqualified_names e1') later_movable_names in
    begin match extract_a_name e2 names_needed with
    | None                                   -> Pexp_sequence (e1', recurse later_movable_names e2)  |> rewrap
    | Some (new_recflag, new_vbs, e2', name) -> Pexp_sequence (e1', e2') |> wrap_with_let_and_continue new_recflag new_vbs name
    end
  | Pexp_letmodule (str_loced, mod_exp, body) ->
    let mod_exp' = rearrange_mod mod_exp in
    let names_needed = List.inter (free_unqualified_names_mod mod_exp') later_movable_names in
    begin match extract_a_name body names_needed with
    | None                                     -> Pexp_letmodule (str_loced, mod_exp', recurse later_movable_names body)  |> rewrap
    | Some (new_recflag, new_vbs, body', name) -> Pexp_letmodule (str_loced, mod_exp', body') |> wrap_with_let_and_continue new_recflag new_vbs name
    end
  | Pexp_ident _
  | Pexp_new   _
  | Pexp_constant _
  | Pexp_extension _
  | Pexp_unreachable                          -> exp
  | Pexp_function cases                       -> rewrap @@ Pexp_function (cases |>@ recurse_case)
  | Pexp_fun (arg_label, default, pat, body)  -> rewrap @@ Pexp_fun (arg_label, default, pat, rearrange_exp body)
  | Pexp_apply (e1, labeled_args)             -> rewrap @@ Pexp_apply (rearrange_exp e1, labeled_args |>@ Tup2.map_snd rearrange_exp)
  | Pexp_match (e, cases)                     -> rewrap @@ Pexp_match (rearrange_exp e, cases |>@ recurse_case)
  | Pexp_try (e, cases)                       -> rewrap @@ Pexp_try (rearrange_exp e, cases |>@ recurse_case)
  | Pexp_array exps                           -> rewrap @@ Pexp_array (exps |>@ rearrange_exp)
  | Pexp_tuple exps                           -> rewrap @@ Pexp_tuple (exps |>@ rearrange_exp)
  | Pexp_construct (lid_loced, e_opt)         -> rewrap @@ Pexp_construct (lid_loced, e_opt |>& rearrange_exp)
  | Pexp_variant (str, e_opt)                 -> rewrap @@ Pexp_variant (str, e_opt |>& rearrange_exp)
  | Pexp_record (fields, e_opt)               -> rewrap @@ Pexp_record (fields |>@ Tup2.map_snd rearrange_exp, e_opt |>& rearrange_exp)
  | Pexp_field (e, lid_loced)                 -> rewrap @@ Pexp_field (rearrange_exp e, lid_loced)
  | Pexp_while (e1, e2)                       -> rewrap @@ Pexp_while (rearrange_exp e1, rearrange_exp e2)
  | Pexp_setfield (e1, lid_loced, e2)         -> rewrap @@ Pexp_setfield (rearrange_exp e1, lid_loced, rearrange_exp e2)
  | Pexp_ifthenelse (e1, e2, e3_opt)          -> rewrap @@ Pexp_ifthenelse (rearrange_exp e1, rearrange_exp e2, e3_opt |>& rearrange_exp)
  | Pexp_for (pat, e1, e2, dirflag, body)     -> rewrap @@ Pexp_for (pat, rearrange_exp e1, rearrange_exp e2, dirflag, rearrange_exp body)
  | Pexp_coerce (e, ct_opt, ct)               -> rewrap @@ Pexp_coerce (rearrange_exp e, ct_opt, ct)
  | Pexp_send (e, str_loced)                  -> rewrap @@ Pexp_send (rearrange_exp e, str_loced)
  | Pexp_setinstvar (str_loced, e)            -> rewrap @@ Pexp_setinstvar (str_loced, rearrange_exp e)
  | Pexp_constraint (e, ct)                   -> rewrap @@ Pexp_constraint (rearrange_exp e, ct)
  | Pexp_assert e                             -> rewrap @@ Pexp_assert (rearrange_exp e)
  | Pexp_lazy e                               -> rewrap @@ Pexp_lazy (rearrange_exp e)
  | Pexp_poly (e, ct_opt)                     -> rewrap @@ Pexp_poly (rearrange_exp e, ct_opt)
  | Pexp_newtype (str_loced, e)               -> rewrap @@ Pexp_newtype (str_loced, rearrange_exp e)
  | Pexp_letexception (exn_ctor, e)           -> rewrap @@ Pexp_letexception (exn_ctor, rearrange_exp e)
  | Pexp_override overrides                   -> rewrap @@ Pexp_override (overrides |>@ Tup2.map_snd rearrange_exp)
  | Pexp_pack mod_exp                         -> rewrap @@ Pexp_pack (rearrange_mod mod_exp)
  | Pexp_object _                             -> failwith "rearrange_exp: classes not handled"
  | Pexp_open (_, _, _)                       -> failwith "rearrange_exp: local opens not handled"


(* let rec rearrange_struct_items defined_names struct_items =
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
    end *)

(* and rearrange_nonrec_vbs defined_names vbs =
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
  vbs', defined_names', names_needed *)

(* and rearrange_exp defined_names exp =
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
    continue exp *)

and rearrange_mod modl =
  let recurse = rearrange_mod in
  match modl.pmod_desc with
  | Pmod_extension _
  | Pmod_ident _                               -> modl
  | Pmod_structure struct_items                -> { modl with pmod_desc = Pmod_structure (rearrange_struct_items struct_items) }
  | Pmod_unpack exp                            -> { modl with pmod_desc = Pmod_unpack (rearrange_exp exp) }
  | Pmod_constraint (mod_exp, mod_type)        -> { modl with pmod_desc = Pmod_constraint (recurse mod_exp, mod_type) }
  | Pmod_functor (name, mod_type_opt, mod_exp) -> { modl with pmod_desc = Pmod_functor (name, mod_type_opt, recurse mod_exp) }
  | Pmod_apply (m1, m2)                        -> { modl with pmod_desc = Pmod_apply (recurse m1, recurse m2) }



(* Only a missing binding to the top level if the name is used in multiple top level bindings OR if the named is used in a top-level let that is not a function. *)
(* Otherwise, add where the name is needed. *)
let rec add_missing_bindings_struct_items defined_names struct_items =
  let open Asttypes in
  let recurse = add_missing_bindings_struct_items in
  let recurse_exp = add_missing_bindings_exp in
  let recurse_mod = add_missing_bindings_mod in
  match struct_items with
  | [] -> []
  | si::rest ->
    let new_binding_y = ref None in
    let add_bindings_and_continue ~pos_opt ~names_for_si ~names_after_si ~names_free_si_rhs ~names_free_si_rhs_that_should_be_top_level ~make_si_desc' =
      (* Position new top level VB near where the binding is needed. *)
      let set_pos vb =
        match pos_opt with
        | Some {Pos.x; y} ->
          begin match !new_binding_y with
          | None   -> new_binding_y := Some (max 0 (y - 10))
          | Some y -> new_binding_y := Some (y + 150)
          end;
          vb |> Pos.set_vb_pos (max 0 (x - 450)) (!new_binding_y ||& y)
        | None -> vb
      in
      let names_needed_si                = List.diff names_free_si_rhs names_for_si in
      let names_needed_remaining_prog    = List.diff (free_unqualified_names_struct_items rest) names_after_si in
      let names_to_define_here           = List.inter names_needed_si names_needed_remaining_prog @ List.inter names_needed_si names_free_si_rhs_that_should_be_top_level |> List.dedup in
      let names_to_define_with_arg_count = names_to_define_here |>@ fun name -> (name, find_arg_count_for_name ~struct_items name) in
      let new_sis                        = names_to_define_with_arg_count |>@ fun (name, arg_count) -> StructItem.value Nonrecursive [Vb.mk (Pat.var name) (make_new_rhs arg_count) |> set_pos] in
      let si'                            = { si with pstr_desc = make_si_desc' (names_to_define_here @ names_for_si) } in
      new_sis @ [si'] @ recurse (names_to_define_here @ names_after_si) rest
    in
    begin match si.pstr_desc with
    | Pstr_eval (exp, attrs) ->
      add_bindings_and_continue
        ~pos_opt:None
        ~names_for_si:defined_names
        ~names_after_si:defined_names
        ~names_free_si_rhs:(free_unqualified_names exp)
        ~names_free_si_rhs_that_should_be_top_level:[]
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_eval (recurse_exp names_for_si' exp, attrs)
        end
    | Pstr_value (Nonrecursive, vbs) ->
      add_bindings_and_continue
        ~pos_opt:(vbs |>@& Pos.vb_pos |> List.sort_by (fun {Pos.x; y} -> (y, x)) |> List.hd_opt)
        ~names_for_si:defined_names
        ~names_after_si:((vbs |>@@ Vb.names) @ defined_names)
        ~names_free_si_rhs:(vbs |>@ Vb.exp |>@@ free_unqualified_names)
        ~names_free_si_rhs_that_should_be_top_level:(vbs |>@ Vb.exp |>@? (Exp.is_fun %> not) |>@@ free_unqualified_names)
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_value (Nonrecursive, vbs |>@ Vb.map_exp (recurse_exp names_for_si'))
        end
    | Pstr_value (Recursive, vbs) ->
      let defined_names' = (vbs |>@@ Vb.names) @ defined_names in
      add_bindings_and_continue
        ~pos_opt:(vbs |>@& Pos.vb_pos |> List.sort_by (fun {Pos.x; y} -> (y, x)) |> List.hd_opt)
        ~names_for_si:defined_names'
        ~names_after_si:defined_names'
        ~names_free_si_rhs:(vbs |>@ Vb.exp |>@@ free_unqualified_names)
        ~names_free_si_rhs_that_should_be_top_level:(vbs |>@ Vb.exp |>@? (Exp.is_fun %> not) |>@@ free_unqualified_names)
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_value (Recursive, vbs |>@ Vb.map_exp (recurse_exp names_for_si'))
        end
    | Pstr_module mod_binding ->
      add_bindings_and_continue
        ~pos_opt:None
        ~names_for_si:defined_names
        ~names_after_si:defined_names
        ~names_free_si_rhs:(free_unqualified_names_mod mod_binding.pmb_expr)
        ~names_free_si_rhs_that_should_be_top_level:[]
        ~make_si_desc':begin fun names_for_si' ->
          Pstr_module { mod_binding with pmb_expr = recurse_mod names_for_si' mod_binding.pmb_expr }
        end
    | Pstr_recmodule mod_bindings ->
      add_bindings_and_continue
        ~pos_opt:None
        ~names_for_si:defined_names
        ~names_after_si:defined_names
        ~names_free_si_rhs:(mod_bindings |>@@ (fun { pmb_expr; _ } -> free_unqualified_names_mod pmb_expr))
        ~names_free_si_rhs_that_should_be_top_level:[]
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
    let names_to_define_with_arg_count = names_needed |>@ fun name -> (name, find_arg_count_for_name ~exp name) in
    List.fold_right
      (fun (name, arg_count) body -> Exp.let_ Asttypes.Nonrecursive [Vb.mk (Pat.var name) (make_new_rhs arg_count)] body)
      names_to_define_with_arg_count
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

and find_arg_count_for_name ?struct_items ?exp name =
  (* Look for uses on application lhs to see if we should make a function skeleton *)
  let arg_count = ref 0 in
  let iter_vis_attrs attrs =
    Vis.all_from_attrs attrs
    |> List.iter begin fun { Vis.exp } ->
      if Exp.simple_name exp = Some name then (* Visualizers have type 'a -> 'b, so a bare name will be applied to one arg. *)
        arg_count := max 1 !arg_count
      else
        arg_count := max !arg_count (find_arg_count_for_name ~exp name)
    end
  in
  let handle_root_pat name_still_visible pat =
    name_still_visible && begin
      pat |> Pat.flatten |> List.iter (fun pat -> iter_vis_attrs pat.ppat_attributes);
      not (List.mem name (Pat.names pat))
    end
  in
  let iter_exp name_still_visible e =
    if name_still_visible then iter_vis_attrs e.pexp_attributes;
    begin match e.pexp_desc with
      | Pexp_apply (fexp, args) when name_still_visible && Exp.simple_name fexp = Some name ->
        arg_count := max !arg_count (List.length args)
      | _ -> ()
    end;
    e
  in
  begin match struct_items, exp with
  | Some struct_items, _ -> ignore @@ map_exps_with_scope_prog true handle_root_pat iter_exp struct_items;
  | _, Some exp          -> ignore @@ map_exps_with_scope      true handle_root_pat iter_exp exp;
  | _                    -> failwith "you were supposed to provide either struct_items or an exp..."
  end;
  !arg_count

(* Based on arg count, generate fun x2 -> fun x1 -> (??) *)
and make_new_rhs arg_count =
  if arg_count = 0
  then Exp.hole
  else Exp.fun_ Asttypes.Nolabel None (Pat.var ("x" ^ string_of_int arg_count)) (make_new_rhs (arg_count - 1))


(*
  Current algorithm for handling extractions (i.e. case introductions.)

  0. Extractions are initially encoded as e.g. let x = f (match (match x with _ -> ...) with _ -> ...), with a single case per match.
  1. New VBs are duplicated into the branches of existing match statements, *because* it makes sense that new things should be created in the context of old things.
    1a. ...with the caveat that new VBs with free vars are only pushed into branches in which those vars are defined
  2. The new match statements are simplified, i.e. a match higher up in the AST may have already scrutinized the same scrutinee,
    if so, we can replace the match with the appropriate branch.
      match x with
      | C1 x1 -> (match x with C1 x2 -> x2)
      ...becomes...
      match x with
      | C1 x1 -> x1
  3. Since new extraction matches have only a single case, that single case might be removed (i.e. we are on a branch on which the extraction cannot apply). Remove such bindings.
  4. Transform matches to the more canonical form.
      f (match (match x with C x1 -> x1) with C y1 -> y1)
      ...becomes...
      match x with
      | C x1 ->
        begin match x1 with
        | C y1 -> f y1
        end
  5. Pull bindings duplicated across all cases into a higher scope. That is, bindings that were inserted into deep branches but don't need the destructured values can be moved back up.
  6. Add missing match cases (since extraction matches are only a single case).
      match x with
      | C x1 ->
        begin match x1 with
        | C y1 -> f y1
        | D -> (??)
        end
      | D -> (??)
`
 *)

(* Duplicate the VB into case branches in which most of its free vars are defined OR into matches that scrutinize matches the vb also scrutinizes. *)
let rec insert_vb_into_all_relevant_branches ?(recflag = Asttypes.Nonrecursive) vb exp =
  let rec names_defined_deeper exp =
    let recurse = names_defined_deeper in
    match exp.pexp_desc with
    | Pexp_let (_, vbs, body)  -> (vbs |>@@ Vb.names) @ recurse body
    | Pexp_sequence (_, e2)    -> recurse e2
    | Pexp_letmodule (_, _, e) -> recurse e
    | Pexp_match (_, cases)    -> cases |>@@ (fun case -> Pat.names case.pc_lhs @ recurse case.pc_rhs)
    | _                        -> []
  in
  let recurse = insert_vb_into_all_relevant_branches vb in
  match exp.pexp_desc with
  | Pexp_let (recflag, vbs, body)           -> { exp with pexp_desc = Pexp_let (recflag, vbs, recurse body) }
  | Pexp_sequence (e1, e2)                  -> { exp with pexp_desc = Pexp_sequence (e1, recurse e2) }
  | Pexp_letmodule (name_loced, mod_exp, e) -> { exp with pexp_desc = Pexp_letmodule (name_loced, mod_exp, recurse e) }
  | Pexp_match (e, cases)                   ->
    let free_names_in_vb =
      let free_names = List.dedup @@ free_unqualified_names_pat vb.pvb_pat @ free_unqualified_names vb.pvb_expr in
      begin match recflag with
      | Asttypes.Nonrecursive -> free_names
      | Asttypes.Recursive    -> List.diff free_names (Vb.names vb)
      end
    in
    (* Find which case(s) define the greatest number of needed names, then push into those. *)
    let cases_and_needed_names_defined_count =
      cases
      |>@ begin fun case ->
        let names_defined_deeper = List.dedup @@ Pat.names case.pc_lhs @ names_defined_deeper case.pc_rhs in
        (case, List.length (List.inter free_names_in_vb names_defined_deeper))
      end
    in
    let most_defined_count = cases_and_needed_names_defined_count |>@ snd |> List.max in
    let cases' =
      cases_and_needed_names_defined_count
      |>@ begin fun (case, needed_names_defined_count) ->
        if needed_names_defined_count = most_defined_count
        then case |> Case.map_rhs recurse
        else case
      end
    in
    { exp with pexp_desc = Pexp_match (e, cases') }
  | _ ->
    Exp.let_ recflag [vb] exp

let move_vbs_into_all_relevant_branches =
  Exp.map begin fun exp ->
    match exp.pexp_desc with
    | Pexp_let (recflag, [vb], body) -> insert_vb_into_all_relevant_branches ~recflag vb body
    | _                              -> exp
  end

let simplify_nested_matches_on_same_thing prog =
  let simplify scrutinee_name branch_pat branch =
    (* Handle shadowing. *)
    let handle_root_pat higher_branch_opt pat = higher_branch_opt |>&& (fun ((scrutinee_name, _) as higher_branch) -> if List.mem scrutinee_name (Pat.names pat) then None else Some higher_branch) in
    branch
    |> map_exps_with_scope (Some (scrutinee_name, branch_pat)) handle_root_pat begin fun higher_branch_opt exp ->
      match higher_branch_opt, exp.pexp_desc with
      (* scrutinee is a simple variable and first pattern is a ctor *)
      | Some (higher_scrutinee_name, higher_branch_pat)
      , Pexp_match ({ pexp_desc = Pexp_ident {txt = Longident.Lident scrutinee_name; _}; _ } as scrutinee, (({ pc_lhs = { ppat_desc = Ppat_construct ({ txt = Longident.Lident _; _ }, _); _}; _}::_) as cases))
      when higher_scrutinee_name = scrutinee_name ->
        (* Find the case that is taken. *)
        (* Three possible results:
        1. One case taken. Replace match with that case.
        2. No case taken. Match is not valid in this branch, remove it entirely (mark for removal by removing all its cases.)
        3. Can't determine which case will be taken. Don't change the match.
        *)
        let exception DontKnow in
        (* Returns case taken and variable substitution, or None if no case take, or raises DontKnow if can't tell *)
        (* Only handles Ctors with variable name children *)
        let pats_match case : (case * string SMap.t) option =
          if case.pc_guard <> None then raise DontKnow else
          begin match higher_branch_pat.ppat_desc, case.pc_lhs.ppat_desc with
          | Ppat_construct ({ txt = Longident.Lident ctor_name1; _ }, args_opt1)
          , Ppat_construct ({ txt = Longident.Lident ctor_name2; _ }, args_opt2) ->
            if ctor_name1 <> ctor_name2 then None else
            begin match args_opt1, args_opt2 with
            | None
            , None ->
              Some (case, SMap.empty)
            | Some _
            , Some { ppat_desc = Ppat_any; _ } ->
              Some (case, SMap.empty)
            | Some { ppat_desc = Ppat_var {txt = higher_name; _}; _ }
            , Some { ppat_desc = Ppat_var {txt = branch_name; _}; _ } ->
              Some (case, SMap.singleton branch_name higher_name)
            | Some { ppat_desc = Ppat_tuple higher_pats; _ }
            , Some { ppat_desc = Ppat_tuple branch_pats; _ } ->
              List.fold_left2 begin fun subst_opt higher_pat branch_pat ->
                if subst_opt = None || Pat.is_any branch_pat then subst_opt else
                begin match Pat.single_name higher_pat, Pat.single_name branch_pat with
                | Some higher_name, Some branch_name -> subst_opt |>& SMap.add branch_name higher_name
                | _                                  -> raise DontKnow
                end
              end (Some SMap.empty) higher_pats branch_pats
              |>& (fun subst -> (case, subst))
            | _ ->
              raise DontKnow
            end
          | _ ->
            raise DontKnow
          end
        in
        begin try
          match cases |> List.findmap_opt pats_match with
          | Some (case, subst) ->
            print_endline (SMap.to_string (fun str -> str) subst);
            rename_unqualified_variables subst case.pc_rhs
          | None ->
            (* No case matches, mark for removal by removing all cases. *)
            { exp with pexp_desc = Pexp_match (scrutinee, []) }
        with DontKnow ->
          exp
        end
      | _ ->
        exp
    end
  in
  prog
  |> Exp.map begin fun exp ->
    match exp.pexp_desc with
    (* scrutinee is a simple variable and first pattern is a ctor *)
    | Pexp_match ({ pexp_desc = Pexp_ident {txt = Longident.Lident scrutinee_name; _}; _ } as scrutinee, (({ pc_lhs = { ppat_desc = Ppat_construct ({ txt = Longident.Lident _; _ }, _); _}; _}::_) as cases)) ->
      let cases' = cases |>@ fun case -> case |> Case.map_rhs (simplify scrutinee_name case.pc_lhs) in
      { exp with pexp_desc = Pexp_match (scrutinee, cases') }
    | _ ->
      exp
  end

(* If an exp in a vb lhs has an empty match, remove the whole vb *)
let remove_matches_with_no_cases prog =
  let rec should_keep exp =
    match exp.pexp_desc with
    | Pexp_let (_, _, e)       -> should_keep e
    | Pexp_sequence (_, e2)    -> should_keep e2
    | Pexp_match (e, cases)    -> cases <> [] && should_keep e
    | Pexp_letmodule (_, _, e) -> should_keep e
    | _                        -> Exp.child_exps exp |> List.for_all should_keep
  in
  prog
  |> VbGroups.map begin fun (recflag, vbs) -> (recflag, vbs |>@? (should_keep %@ Vb.exp)) end
  |> VbGroups.SequenceLike.map (fun imperative_exp -> Some imperative_exp |>&? should_keep)


let move_up_duplicated_bindings prog =
  (* nondep = not dependent on the case pat OR anything defined earlier in the case branch *)
  (* If we iteratively pluck out such letexps one by one we will catch nondep chains. *)
  let find_nondep_letexps case =
    let rec find_nondep_letexps names exp =
      let recurse = find_nondep_letexps in
      match exp.pexp_desc with
      | Pexp_let (Asttypes.Nonrecursive, vbs, body) ->
        let names_here = vbs |>@@ Vb.names in
        if (vbs |> List.for_all (not %@ List.any_overlap names %@ free_unqualified_names %@ Vb.exp))
        then exp :: recurse (names_here @ names) body
        else        recurse (names_here @ names) body
      | Pexp_let (Asttypes.Recursive, vbs, body) ->
        let names_here = vbs |>@@ Vb.names in
        let names = List.diff names names_here in
        if (vbs |> List.for_all (not %@ List.any_overlap names %@ free_unqualified_names %@ Vb.exp))
        then exp :: recurse (names_here @ names) body
        else        recurse (names_here @ names) body
      | Pexp_sequence (_, e2)    -> recurse names e2 (* could move these out... *)
      | Pexp_letmodule (_, _, e) -> recurse names e
      | _                        -> []
    in
    find_nondep_letexps (Pat.names case.pc_lhs) case.pc_rhs
  in
  let vbs_equal vb1 vb2 = Vb.to_string (Attrs.remove_all_deep_vb vb1) = Vb.to_string (Attrs.remove_all_deep_vb vb2) in
  let letexps_equal e1 e2 =
    match e1.pexp_desc, e2.pexp_desc with
    | Pexp_let (recflag1, vbs1, _body1)
    , Pexp_let (recflag2, vbs2, _body2) ->
      recflag1 = recflag2 && List.for_all2_safe vbs_equal vbs1 vbs2
    | _ ->
      false
  in
  let rec remove_letexp letexp exp =
    let recurse = remove_letexp letexp in
    match exp.pexp_desc with
    | Pexp_let (_, _, body) when letexps_equal exp letexp -> body
    | Pexp_let (recflag, vbs, body)                       -> { exp with pexp_desc = Pexp_let (recflag, vbs, recurse body) }
    | Pexp_sequence (e1, e2)                              -> { exp with pexp_desc = Pexp_sequence (e1, recurse e2) }
    | Pexp_letmodule (name_loced, mod_exp, e)             -> { exp with pexp_desc = Pexp_letmodule (name_loced, mod_exp, recurse e) }
    | _                                                   -> exp
  in
  let letexp_is_in_list letexp list = List.exists (letexps_equal letexp) list in
  prog
  |> Exp.map begin fun exp ->
    match exp.pexp_desc with
    | Pexp_match (scrutinee, ((_::_) as cases)) ->
      let rec loop extracted_letexps letexps_to_ignore cases' =
        (* Find a letexp we haven't inspected yet. *)
        let extraction_candidate =
          find_nondep_letexps (List.hd cases')
          |> List.find_opt (fun letexp -> not (letexp_is_in_list letexp letexps_to_ignore))
        in
        begin match extraction_candidate with
        | Some letexp ->
          (* If the letexp exists in all other branches AND is nondep in all other branches, then we can move it out. *)
          if (cases' |> List.for_all (fun case -> letexp_is_in_list letexp (find_nondep_letexps case))) then
            let cases' = cases' |>@ Case.map_rhs (remove_letexp letexp) in
            loop (letexp::extracted_letexps) letexps_to_ignore cases'
          else
            loop extracted_letexps (letexp::letexps_to_ignore) cases'
        | None ->
          (* Loop done. Wrap match with extraced vbs *)
          let extracted_vb_groups =
            extracted_letexps
            |>@ begin fun letexp ->
              match letexp.pexp_desc with
              | Pexp_let (recflag, vbs, _) -> (recflag, vbs)
              | _                          -> failwith "move_up_duplicated_bindings: shouldn't happen"
            end
          in
          List.fold_right
            (fun (recflag, vbs) e -> Exp.let_ recflag vbs e)
            extracted_vb_groups
            { exp with pexp_desc = Pexp_match (scrutinee, cases') }
        end
      in
      loop [] [] cases
    | _ ->
      exp
  end


(* Drag-to-extract produces a "let subvalue2 = subvalue in" binding, which is superfluous because
name patterns in cases are shown as TVs on the canvas (becuase the above is ugly). Remove these bindings.

(And copy their [@pos] attr to the pattern.)
*)
let remove_simple_rename_bindings prog =
  let init_name_to_pat = [] in (* Association list of (name, pat) *)
  let handle_root_pat name_to_pat pat =
    let introduced =  Pat.flatten pat |>@? Pat.is_name |>@ (fun pat -> (Pat.name pat ||& "", pat)) in
    introduced @ name_to_pat
  in
  let patterns_to_position = ref [] in (* List of (pat, Pos.t) *)
  prog
  |> map_exps_with_scope_prog init_name_to_pat handle_root_pat begin fun name_to_pat exp ->
    match exp.pexp_desc with
    (* let lhs_name = rhs_name in *)
    | Pexp_let (Asttypes.Nonrecursive, [{pvb_pat; pvb_expr; pvb_attributes; _}], body) when Pat.is_single_name pvb_pat && Exp.is_ident pvb_expr ->
      begin match (Pat.single_name pvb_pat, Exp.simple_name pvb_expr) with
      | Some lhs_name, Some rhs_name
        when List.mem_assoc rhs_name name_to_pat (* This is a simple renaming *)
          && not @@ List.mem lhs_name (free_unqualified_names body) (* Name lhs_name unused *)
          ->
        let higher_pat = List.assoc rhs_name name_to_pat in
        (* Note the pos attrs so we can copy it to the pat. *)
        begin match Pos.from_attrs pvb_attributes with
        | Some pos -> patterns_to_position := (higher_pat, pos) :: !patterns_to_position
        | _        -> ()
        end;
        (* Remove the binding *)
        body
      | _ ->
        exp
      end
    | _ ->
      exp
  end
  (* |> begin fun prog ->
    !patterns_to_position |> List.iter begin fun (pat, pos) ->
      print_endline @@ Pat.to_string pat ^ " " ^ Exp.to_string (Pos.set_exp_pos pos.Pos.x pos.y (Exp.var "x"))
    end;
    prog
  end *)
  (* Copy positions to the pattern *)
  |> Pat.map begin fun pat ->
    match List.assoc_opt pat !patterns_to_position with
    | Some pos -> Pos.(set_pat_pos pos.x pos.y pat)
    | None     -> pat
  end


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
  (* Uncomment the log lines to see how all this works *)
  (* let log prog = print_endline (Shared.Formatter_to_stringifier.f Pprintast.structure prog); prog in *)
  prog
  (* |> log *)
  |> move_vbs_into_all_relevant_branches (* VBs pushed down (duplicated) across branches *)
  (* |> log *)
  |> simplify_nested_matches_on_same_thing (* A match statement may have been inserted inside a match branch that already matches on the same scrutinee. Simplify. *)
  (* |> log *)
  |> remove_matches_with_no_cases (* Nested extraction not valid on this branch *)
  (* |> log *)
  |> move_matches_outside (* Transform the "let x = match (match x with ...) with ... in" structure by floating the matches outward. *)
  (* |> log *)
  |> move_up_duplicated_bindings (* Since we duplicated VBs, pull them back out. *)
  (* |> log *)
  |> add_missing_cases final_tenv
  (* |> log *)
  |> remove_simple_rename_bindings (* We affect the "Destruct" button by inserting "let x = match y with ... -> z" to trigger the above mechanics, which preserves the match an ultimately simplifies the binding to "let x = z". Remove that binding. *)
  (* |> log *)

let remove_rejection_attrs_no_longer_on_holes prog =
  prog
  |> Exp.map begin fun e ->
    if Exp.is_hole e || Attr.has_tag "accept_or_reject" e.pexp_attributes
    then e
    else { e with pexp_attributes = Attr.remove_name "not" e.pexp_attributes }
  end

(* Need final tenv to know what constructors exist *)
let fixup_ defined_names final_tenv prog =
  prog
  |> fixup_matches final_tenv
  |> move_type_decls_to_top
  |> rearrange_struct_items
  |> add_missing_bindings_struct_items defined_names
  |> remove_rejection_attrs_no_longer_on_holes

let synth_fixup_ prog =
  (* TODO only do first steps for struct items with holes *)
  (* Uncomment the log lines to see how all this works *)
  (* let log prog = print_endline (Shared.Formatter_to_stringifier.f Pprintast.structure prog); prog in *)
  prog
  (* |> log *)
  |> move_vbs_into_all_relevant_branches (* VBs pushed down (duplicated) across branches *)
  (* |> log *)
  |> move_up_duplicated_bindings (* Since we duplicated VBs, pull them back out. *)
  (* |> log *)
  |> rearrange_struct_items
  (* |> log *)

let initial_defined_names = SSet.elements Name.pervasives_names

let fixup final_tenv prog =
  prog
  |> fixup_ initial_defined_names final_tenv
  |> fixup_ initial_defined_names final_tenv
  |> fixup_ initial_defined_names final_tenv

let synth_fixup prog =
  (* let log prog = print_endline ("HIII\n" ^ Shared.Formatter_to_stringifier.f Pprintast.structure prog); prog in *)
  prog
  (* |> log *)
  |> synth_fixup_
  |> synth_fixup_


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
