(*
  Actions generated from the browser and set to server.
  Need to keep format in sync in maniposynth.js
*)

type t =
  | AddCodeToScopeBindings of string * Ast_id.t
  [@@deriving yojson]

module Migrate_ast = Ocamlformat_lib.Migrate_ast
module Ast_mapper  = Ocamlformat_lib.Migrate_ast.Ast_mapper
module Parsetree   = Ocamlformat_lib.Migrate_ast.Parsetree
module Ast_builder = Ocamlformat_lib.Migrate_ast.Selected_version.Ast_helper (* Make(struct let loc = Location.none end) *)

let default_mapper = Ast_mapper.default_mapper

(* Bottom up: f applied to leaves first. *)
let map_exp_by_id ~id ~f toplevel_phrases =
  let replacer mapper expr =
    let expr' = default_mapper.expr mapper expr in
    if Ast_id.has_id id ~expr:expr'
    then f expr'
    else expr'
  in
  let mapper = { default_mapper with expr = replacer } in
  let open Parsetree in
  toplevel_phrases
  |> List.map (function
      | Ptop_def structure -> Ptop_def (mapper.structure mapper structure)
      | Ptop_dir directive -> Ptop_dir directive
  )

(* let replace_exp_by_id ~id ~new_expr toplevel_phrases =
  map_exp_by_id id (fun _ -> new_expr) toplevel_phrases *)

let parse_expr code : Parsetree.expression =
  Lexing.from_string code
  |> Migrate_parsetree.Parse.expression Migrate_ast.selected_version

let add_exp_to_scope_bindings ~expr' ~scope_id toplevel_phrases =
  let open Parsetree in
  let rec f expr =
    match expr.pexp_desc with
    | Pexp_let (Recursive, vbs, body_expr) ->
        let pat    = Ast_builder.Pat.var (Location.mknoloc "_") in
        let new_vb = Ast_builder.Vb.mk pat expr' in
        { expr with pexp_desc = Pexp_let (Recursive, vbs @ [new_vb], body_expr) }
    | Pexp_let (Nonrecursive, vbs, body_expr) ->
        { expr with pexp_desc = Pexp_let (Nonrecursive, vbs, f body_expr) }
    | _ ->
        let pat    = Ast_builder.Pat.var (Location.mknoloc "_") in
        let new_vb = Ast_builder.Vb.mk pat expr' in
        Ast_builder.Exp.let_ Recursive [new_vb] expr
  in
  map_exp_by_id ~id:scope_id ~f toplevel_phrases

let f file_path action =
  match action with
  | AddCodeToScopeBindings (new_code, scope_id) ->
    let parsed_with_comments = Parse_unparse.parse_file file_path in
    let expr' = parse_expr new_code in
    let ast' = add_exp_to_scope_bindings ~expr' ~scope_id parsed_with_comments.ast in
    let parsed_with_comments' = { parsed_with_comments with ast = ast' } in
    let new_file_code = Parse_unparse.unparse file_path parsed_with_comments' in
    Utils.save_file file_path new_file_code
