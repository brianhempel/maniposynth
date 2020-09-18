(*
  Actions generated from the browser and set to server.
  Need to keep format in sync in maniposynth.js
*)

type t =
  | AddCodeToScopeBindings of string * string (* code str and scope id str *)
  | ReplaceCodeAtExpr of string * string (* code str and ast id str *)
  [@@deriving yojson]

module Parsetree   = Ocamlformat_lib.Migrate_ast.Parsetree
module Ast_helper  = Ocamlformat_lib.Migrate_ast.Selected_version.Ast_helper

let unique_var_name base_name toplevel_phrases =
  let names_ref = ref [] in
  let open Ast_iterator in
  let iterator =
    let iter_pat iter pat =
      default_iterator.pat iter pat;
      match Ast_utils.Pat.get_var_name_opt pat with
      | Some name -> names_ref := name :: !names_ref
      | None      -> () 
    in
    let iter_expr iter expr =
      default_iterator.expr iter expr;
      match expr.pexp_desc with
      | Parsetree.Pexp_ident { txt = longident; _ } ->
          names_ref := (Longident.last longident) :: !names_ref
      | _ ->
          ()
    in
    { default_iterator with pat = iter_pat; expr = iter_expr }
  in
  Ast_utils.apply_iterator_to_toplevel_phrases iterator toplevel_phrases;
  let used_names = !names_ref in
  let rec loop n =
    let candidate = base_name ^ string_of_int n in
    if List.mem candidate used_names
    then loop (n + 1)
    else candidate
  in
  loop 1

let suggested_name_for_expr expr =
  expr
  |> (Utils.formatter_to_stringifyer Pprintast.expression)
  |> String.trim
  |> String.lowercase_ascii
  |> String_utils.parameterize
  |> String.split_on_char '_'
  |> List.filter (fun str -> String.length str > 0 && Char_utils.is_letter str.[0])
  |> String.concat "_"
  |> (function | "" -> "var" | str -> str)


let add_exp_to_scope_bindings ~expr' ~scope_id toplevel_phrases =
  let open Parsetree in
  let name = unique_var_name (suggested_name_for_expr expr') toplevel_phrases in
  let pat    = Ast_utils.Pat.var name in
  let new_vb = Ast_helper.Vb.mk pat expr' in
  let rec f expr =
    match expr.pexp_desc with
    | Pexp_let (Recursive, vbs, body_expr) ->
        { expr with pexp_desc = Pexp_let (Recursive, vbs @ [new_vb], body_expr) }
    | Pexp_let (Nonrecursive, vbs, body_expr) ->
        { expr with pexp_desc = Pexp_let (Nonrecursive, vbs, f body_expr) }
    | _ ->
        Ast_helper.Exp.let_ Recursive [new_vb] expr
  in
  Ast_utils.map_expr_by_id ~expr_id:scope_id ~f toplevel_phrases

let f file_path action =
  let parsed_with_comments = Parse_unparse.parse_file file_path in
  let ast' = 
    match action with
    | AddCodeToScopeBindings (new_code, scope_id_str) ->
      let expr' = Ast_utils.Exp.of_string new_code in
      let scope_id = Ast_id.t_of_string scope_id_str in
      add_exp_to_scope_bindings ~expr' ~scope_id parsed_with_comments.ast
    | ReplaceCodeAtExpr (new_code, expr_id_str) ->
      let expr' = Ast_utils.Exp.of_string new_code in
      let expr_id = Ast_id.t_of_string expr_id_str in
      Ast_utils.replace_expr_by_id ~expr_id ~expr' parsed_with_comments.ast
  in
  let parsed_with_comments' = { parsed_with_comments with ast = ast' } in
  let new_file_code = Parse_unparse.unparse file_path parsed_with_comments' in
  Sys_utils.save_file file_path new_file_code

