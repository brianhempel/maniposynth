module Migrate_ast = Ocamlformat_lib.Migrate_ast
module Ast_mapper  = Ocamlformat_lib.Migrate_ast.Ast_mapper
module Parsetree   = Ocamlformat_lib.Migrate_ast.Parsetree

let default_mapper = Ast_mapper.default_mapper

(* Bottom up: f applied to leaves first. *)
let map_expr_by_id ~expr_id ~f toplevel_phrases =
  let replacer mapper expr =
    let expr' = default_mapper.expr mapper expr in
    if Ast_id.has_id expr_id ~expr:expr'
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

let replace_expr_by_id ~expr_id ~expr' toplevel_phrases =
  map_expr_by_id ~expr_id ~f:(fun _ -> expr') toplevel_phrases

let parse_expr code : Parsetree.expression =
  Lexing.from_string code
  |> Migrate_parsetree.Parse.expression Migrate_ast.selected_version

let longident name =
  Option.get (Longident.unflatten [name])

let longident_loced name =
  Location.mknoloc (longident name)

module Exp = struct

  let var name =
    Ast_helper.Exp.ident ~loc:Location.none (longident_loced name)

end
