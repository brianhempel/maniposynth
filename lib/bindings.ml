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
  1. For each unsatisfied binding, find the binding (if any)
     that should be in scope for it.
  2. For each binding, if all its intended uses are not in scope, move the binding up.
  3. Repeat, but check for cycles.

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

let rec free_unqualified_names exp =
  let recurse = free_unqualified_names in
  let free_unqualified_names_case { pc_lhs; pc_guard; pc_rhs } =
    List.diff
      ((pc_guard |>& recurse ||& []) @ recurse pc_rhs)
      (Pat.names pc_lhs)
  in
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
      (vbs |>@ Vb.exp |>@@ recurse) @
      List.diff
        (recurse body)
        (vbs |>@@ Vb.names)
  | Pexp_let (Asttypes.Recursive, vbs, body) ->
      List.diff
        ((vbs |>@ Vb.exp |>@@ recurse) @ recurse body)
        (vbs |>@@ Vb.names)
  | Pexp_function cases ->
      cases |>@@ free_unqualified_names_case
  | Pexp_fun (_, default, pat, body) ->
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
        (vbs |>@ Vb.exp |>@@ recurse_exp) @
        List.diff
          later_names
          (vbs |>@@ Vb.names)
    | Pstr_value (Asttypes.Recursive, vbs) ->
        List.diff
          ((vbs |>@ Vb.exp |>@@ recurse_exp) @ later_names)
          (vbs |>@@ Vb.names)
    | Pstr_primitive _
    | Pstr_type (_, _)
    | Pstr_typext _
    | Pstr_modtype _
    | Pstr_class_type _
    | Pstr_include _
    | Pstr_attribute _
    | Pstr_extension (_, _)
    | Pstr_exception _ ->
        later_names
    | Pstr_module { pmb_expr; _ } ->
        free_unqualified_names_mod pmb_expr @ later_names
    | Pstr_recmodule mod_bindings ->
        (mod_bindings |>@@ (fun { pmb_expr; _ } -> free_unqualified_names_mod pmb_expr)) @ later_names
    | Pstr_open _ ->
        failwith "free_unqualified_names_struct_items: opens not handled"
    | Pstr_class _ ->
        failwith "free_unqualified_names_struct_items: classes not handled"
    end


let rec fixup_top_level defined_names struct_items =
  let recurse ?(defined_names = defined_names) = fixup_top_level defined_names in
  match struct_items with
  | [] -> []
  | si::rest ->
    begin match si.pstr_desc with
    | Pstr_eval (exp, _) ->
      let names_needed = List.diff (free_unqualified_names exp) defined_names in
      begin match names_needed with
      | []      -> si :: recurse rest
      | name::_ ->
        begin match extract_vb_with_name rest with
        | None ->
          let vb = Vb.mk (Pat.var name) Exp.hole in
          recurse (StructItem.value Asttypes.Nonrecursive [vb] :: struct_items)
        | Some (vb, rest') ->
          recurse (StructItem.value Asttypes.Nonrecursive [vb] :: si :: rest')
        end
      end
    | Pstr_value (Asttypes.Nonrecursive, vbs) ->
       (* START HERE *)
    | Pstr_value (Asttypes.Recursive, vbs) -> (??)
    | Pstr_primitive _ -> (??)
    | Pstr_type (_, _) -> (??)
    | Pstr_typext _ -> (??)
    | Pstr_exception _ -> (??)
    | Pstr_module _ -> (??)
    | Pstr_recmodule _ -> (??)
    | Pstr_modtype _ -> (??)
    | Pstr_open _ -> (??)
    | Pstr_class _ -> (??)
    | Pstr_class_type _ -> (??)
    | Pstr_include _ -> (??)
    | Pstr_attribute _ -> (??)
    | Pstr_extension (_, _) -> (??)
    end


let fixup prog =
  fixup_top_level [] prog


let _ =
  let prog = StructItems.from_string "let x = y\nlet y = 10" in
  fixup prog |> StructItems.to_string |> print_endline
