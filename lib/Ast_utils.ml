open Utils

module Migrate_ast = Ocamlformat_lib.Migrate_ast
module Ast_mapper  = Ocamlformat_lib.Migrate_ast.Ast_mapper
module Parsetree   = Ocamlformat_lib.Migrate_ast.Parsetree

(* Reminder: type structure = structure_item list *)

let structure_of_toplevel_phrases (phrases : Parsetree.toplevel_phrase list) : Parsetree.structure =
  let open Parsetree in
  phrases
  |> List.concat_map (function
      | Ptop_def structure_items -> structure_items
      | Ptop_dir _directive      -> failwith "structure_of_toplevel_phrases cannot handle toplevel directive (Ptop_dir)"
  )

let toplevel_phrases_of_structure structure =
  [ Parsetree.Ptop_def structure ]

let default_mapper = Ast_mapper.default_mapper

let apply_mapper_to_toplevel_phrases (mapper : Ast_mapper.mapper) toplevel_phrases =
  let open Parsetree in
  toplevel_phrases
  |> List.map (function
      | Ptop_def structure -> Ptop_def (mapper.structure mapper structure)
      | Ptop_dir directive -> Ptop_dir directive
  )  

(* Bottom up: f applied to leaves first. *)
let map_expr_by_id ~expr_id ~f toplevel_phrases =
  let replacer mapper expr =
    let expr' = default_mapper.expr mapper expr in
    if Ast_id.has_id expr_id ~expr:expr'
    then f expr'
    else expr'
  in
  let mapper = { default_mapper with expr = replacer } in
  apply_mapper_to_toplevel_phrases mapper toplevel_phrases

let replace_expr_by_id ~expr_id ~expr' toplevel_phrases =
  map_expr_by_id ~expr_id ~f:(fun _ -> expr') toplevel_phrases

let longident name =
  Option.get (Longident.unflatten [name])

let longident_loced name =
  Location.mknoloc (longident name)

module Exp = struct
  open Parsetree

  let var name =
    Ast_helper.Exp.ident ~loc:Location.none (longident_loced name)

  let string = Ast_helper.Exp.constant % Ast_helper.Const.string

  let of_string code =
    Lexing.from_string code
    |> Migrate_parsetree.Parse.expression Migrate_ast.selected_version
  
  let is_fun expr = match expr.pexp_desc with Pexp_fun _ -> true | _ -> false
end


module Pat = struct

  let get_var_name_opt (pattern : Parsetree.pattern) =
    match pattern.ppat_desc with
    | Parsetree.Ppat_var name_loced -> Some name_loced.txt
    | _                             -> None

end

module Type = struct
  (* Btype.fold_type_expr only applys f to the immediate children. *)
  let deep_fold_type_expr f init typ =
    let rec f' acc typ =
      let acc' = Btype.fold_type_expr f' acc typ in
      f acc' typ
    in
    f' init typ

end