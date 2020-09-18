open Ocamlformat_lib.Migrate_ast.Parsetree
open Utils

type branch_path = int list

type t =
  | Constant of branch_path * expression

  | Unknown

  (* expr is the scope, the outermost expression (usually a let) *)
  | Bindings_rets of expression * binding_skel list * t list 

  | Fun of branch_path * Asttypes.arg_label * expression option * pattern * t

  (* (apply_expr, fun_expr, arg_skels). can have 0 arguments, e.g. bare variable usage (var does not have have function type) *)
  | Apply of branch_path * expression * expression * (Asttypes.arg_label * t) list 

  | Construct of branch_path * expression * Longident.t * t option

and binding_skel = branch_path * value_binding * t

let string_of_branch_path = List.map string_of_int %> String.concat "."
let branch_path_of_string = String.split_on_char '.' %> List.map int_of_string

(* for debugging *)
let rec show = function
  | Constant (_, expr) -> "Constant " ^ Show_ast.expr expr
  | Unknown           -> "Unknown"
  | Fun (_, arg_label, default_opt, pat, body_skel)  ->
    let dummy_fun = { Show_ast.dummy_expr with pexp_desc = Pexp_fun (arg_label, default_opt, pat, Show_ast.dummy_expr) } in
    Show_ast.expr dummy_fun ^ show body_skel
  | Apply (_, _, _, _) -> "app lololol"
  | Construct (_, _, _, _) -> "construct lololol"
  | Bindings_rets (_, bindings_skels, ret_skels) ->
    let binding_strs = List.map show_binding bindings_skels in
    "let " ^ String.concat " and " binding_strs ^ " in (" ^ String.concat " | " (List.map show ret_skels) ^  ")"
and
  show_binding (_, { pvb_pat = pat; _ }, skel) = Show_ast.pat pat ^ " = " ^ show skel


let apply_renamings renamings expr =
  expr
  |> Ast_utils.Exp.map (fun ({ pexp_desc; _ } as expr) ->
      match pexp_desc with
      | Pexp_ident { txt = longident; loc } ->
          let name = Show_ast.longident longident in
          (match List.assoc_opt name renamings with
          | Some name' -> { expr with pexp_desc = Pexp_ident { txt = Lident name'; loc = loc } }
          | None       -> expr
          )
      | _ ->
          expr
  )

(* Assumes all vars in expr have unique names. *)
let destruction_renamings_of_expr expr =
  let renamings_ref = ref [] in
  let iterate iterate_deeper { pexp_desc; _ } =
    match pexp_desc with
    | Pexp_match (scrutinee_expr, cases) ->
        let renamings = !renamings_ref in
        let more_renamings =
          let base_name = Show_ast.expr (apply_renamings renamings scrutinee_expr) in
          cases
          |> List.concat_map (fun case -> case.pc_lhs |> Ast_utils.Pat.all_var_names)
          |> List.map (fun name -> (name, base_name ^ "↯" ^ name)) (* ➘⬇︎⤵︎↴↓↯ *)
        in
        renamings_ref := more_renamings @ !renamings_ref;
        iterate_deeper ()

    | _ -> 
      iterate_deeper ()
  in
  Ast_utils.Exp.iter iterate expr;
  !renamings_ref


let rec skel_of_expr branch_path ({ pexp_desc = exp_desc; _ } as expr) =
  let recurse = skel_of_expr branch_path in
  let ensure_bindings_rets scope_expr  = function
    | (Bindings_rets _) as skel -> skel
    | other_skel -> Bindings_rets (scope_expr, [], [other_skel])
  in
  let append_bindings_rets scope_expr l_skel r_skel =
    match (ensure_bindings_rets scope_expr l_skel, ensure_bindings_rets scope_expr r_skel) with
    | ( Bindings_rets (_, l_bindings_skels, l_rets)
      , Bindings_rets (_, r_bindings_skels, r_rets)
      ) -> Bindings_rets (scope_expr, l_bindings_skels @ r_bindings_skels, l_rets @ r_rets)
    | _ -> failwith "impossible: ensure_bindings_rets ensures the skeleton is a bindings_rets"
  in
  match exp_desc with
  | Pexp_ident _ -> Apply (branch_path, expr, expr, [])
  | Pexp_constant _constant -> Constant (branch_path, expr)
  | Pexp_let (_rec_flag, value_bindings, body_expr) ->
      let bindings_skels = List.map (fun vb -> (branch_path, vb, skeleton_of_value_binding branch_path vb)) value_bindings in
      (* flatten multiple lets together *)
      (match recurse body_expr with
      | Bindings_rets (_, deeper_bindings_skels, rets) -> 
          Bindings_rets (expr, bindings_skels @ deeper_bindings_skels, rets)
      | body_skel -> Bindings_rets (expr, bindings_skels, [body_skel])
      )
  | Pexp_fun (arg_label, default_opt, pat, body_expr) ->
      (* ensure function body is a Bindings_rets, so there's a blank space in the interface for the user to add bindings *)
      (match recurse body_expr with
      | Fun _ as body_skel ->
          Fun (branch_path, arg_label, default_opt, pat, body_skel)
      | body_skel ->
          Fun (branch_path, arg_label, default_opt, pat, ensure_bindings_rets body_expr body_skel)
      )
  | Pexp_apply (fun_expr, arg_labels_exps) ->
      let arg_labels_skels = List.map (fun (l, e) -> (l, recurse e)) arg_labels_exps in
      Apply (branch_path, expr, fun_expr, arg_labels_skels)
  | Pexp_match (_scrutinee_expr, cases) ->
    let branch_skels =
      List.mapi (fun i case -> skel_of_expr (branch_path @ [i]) case.pc_rhs) cases
    in
    (match branch_skels with
    | first::rest -> List.fold_left (append_bindings_rets expr) first rest
    | []          -> failwith "impossible: match statement should have at least one branch"
    )
  | Pexp_construct (ident_located, exp_opt) ->
    Construct (branch_path, expr, ident_located.txt, Option.map recurse exp_opt)
  | _ -> Unknown
and skeleton_of_value_binding branch_path { pvb_pat = _; pvb_expr = expr; _ } = skel_of_expr branch_path expr

let bindings_skels_of_structure_item ({pstr_desc=structure_item_desc; _} : structure_item) : binding_skel list =
  match structure_item_desc with
  | Pstr_value (_, value_bindings) ->
      List.map (fun vb -> ([0], vb, skeleton_of_value_binding [0] vb)) value_bindings
  | _ -> []

let bindings_skels_of_toplevel_phrase (phrase : toplevel_phrase) : binding_skel list =
  match phrase with
  | Ptop_def structure_items -> List.concat_map bindings_skels_of_structure_item structure_items
  | Ptop_dir _               -> []

type phrases = toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments

let bindings_skels_of_parsed_with_comments ({ ast = toplevel_phrases; _ } : phrases) : binding_skel list = 
  List.concat_map bindings_skels_of_toplevel_phrase toplevel_phrases
