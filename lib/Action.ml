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

let add_exp_to_scope_bindings ~expr' ~scope_id toplevel_phrases =
  let open Parsetree in
  let rec f expr =
    match expr.pexp_desc with
    | Pexp_let (Recursive, vbs, body_expr) ->
        let pat    = Ast_helper.Pat.var (Location.mknoloc "_") in
        let new_vb = Ast_helper.Vb.mk pat expr' in
        { expr with pexp_desc = Pexp_let (Recursive, vbs @ [new_vb], body_expr) }
    | Pexp_let (Nonrecursive, vbs, body_expr) ->
        { expr with pexp_desc = Pexp_let (Nonrecursive, vbs, f body_expr) }
    | _ ->
        let pat    = Ast_helper.Pat.var (Location.mknoloc "_") in
        let new_vb = Ast_helper.Vb.mk pat expr' in
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

