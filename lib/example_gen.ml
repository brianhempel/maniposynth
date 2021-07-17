open Shared.Ast
open Shared.Util

let bare_lits =
  [ (Predef.type_int,  List.init 10 (fun n -> Exp.int_lit n))
  ; (Predef.type_bool, [Exp.simple_var "true"; Exp.simple_var "false"])
  ]

let rec examples size_limit tenv typ =
  if size_limit <= 0 then [] else
  let open Type in
  let open Types in
  (* Only return lit 0 for type variable. *)
  if Type.is_var_type typ then [(Exp.int_lit 0, Predef.type_int)] else
  match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) bare_lits with
  | Some lits -> [(List.hd lits, typ)]
  | None ->
    let ctor_descs = Env.fold_constructors List.cons None(* not looking in a nested module *) tenv [] in
    ctor_descs
    |>@@ begin fun { cstr_args; cstr_res; cstr_name; _ } ->
      if is_exn_type cstr_res then [] else (* Ignore exceptions. *)
      if not (does_unify typ cstr_res) then [] else
      let ctor_type_as_arrows  = unflatten_arrows (cstr_args @ [cstr_res]) in
      let target_type_as_arrow = unflatten_arrows ((cstr_args |>@ fun _ -> new_var ()) @ [typ]) in
      match unify_opt ctor_type_as_arrows target_type_as_arrow with
      | None -> []
      | Some type_as_arrows' ->
        if cstr_args = [] then [(Exp.ctor cstr_name [], cstr_res)] else
        (* Ctor w/args counts as AST size 2, one for "apply", one for "apply" LHS *)
        ctor_arg_candidates (size_limit-2) tenv type_as_arrows'
        |>@ begin fun (args, type_as_arrows'') ->
          (Exp.ctor cstr_name args, List.last (flatten_arrows type_as_arrows''))
        end
    end

and ctor_arg_candidates size_limit tenv type_as_arrows =
  if size_limit <= 0 then [] else
  let open Type in
  match flatten_arrows type_as_arrows with
  | [] -> assert false
  | [_] -> [([], type_as_arrows)]
  | arg_t::rest ->
    examples size_limit tenv arg_t
    |>@@ begin fun (arg, arg_t') ->
      match unify_opt (unflatten_arrows (arg_t'::rest)) type_as_arrows with
      | None -> []
      | Some type_as_arrows' ->
        let arg_size = Synth.exp_size arg in
        (* Chop off one arg *)
        let rest_as_arrows = type_as_arrows' |> flatten_arrows |> List.tl |> unflatten_arrows in
        ctor_arg_candidates (size_limit - arg_size) tenv rest_as_arrows
        |>@& begin fun (args, rest_as_arrows'') ->
          (* this final unification may be unecessary if examples always returns concrete types *)
          unify_opt type_as_arrows' (arrow arg_t' rest_as_arrows'')
          |>& fun type_as_arrows'' -> (arg::args, type_as_arrows'')
        end
    end
