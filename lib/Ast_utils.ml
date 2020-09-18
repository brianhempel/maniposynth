open Utils
open Name_utils

module Migrate_ast  = Ocamlformat_lib.Migrate_ast
module Ast_mapper   = Ocamlformat_lib.Migrate_ast.Ast_mapper
module Parsetree    = Ocamlformat_lib.Migrate_ast.Parsetree

(* Reminder: type Parsetree.structure = structure_item list *)

let structure_of_toplevel_phrases (phrases : Parsetree.toplevel_phrase list) : Parsetree.structure =
  let open Parsetree in
  phrases
  |> List.concat_map (function
      | Ptop_def structure_items -> structure_items
      | Ptop_dir _directive      -> failwith "structure_of_toplevel_phrases cannot handle toplevel directive (Ptop_dir)"
  )

let toplevel_phrases_of_structure structure =
  [ Parsetree.Ptop_def structure ]

let default_mapper   = Ast_mapper.default_mapper
let default_iterator = Ast_iterator.default_iterator

let apply_mapper_to_toplevel_phrases (mapper : Ast_mapper.mapper) toplevel_phrases =
  let open Parsetree in
  toplevel_phrases
  |> List.map (function
      | Ptop_def structure -> Ptop_def (mapper.structure mapper structure)
      | Ptop_dir directive -> Ptop_dir directive
  )

let apply_iterator_to_toplevel_phrases (iterator : Ast_iterator.iterator) toplevel_phrases =
  let open Parsetree in
  toplevel_phrases
  |> List.iter (function
      | Ptop_def structure  -> iterator.structure iterator structure
      | Ptop_dir _directive -> ()
  )

(* Bottom up. *)
let expr_mapper f =
  let replacer mapper expr =
    let expr' = default_mapper.expr mapper expr in
    f expr'
  in
  { default_mapper with expr = replacer }

(* A thunk to iterate deeper is passed to f, so you can control iteration order. *)
let expr_iterator f =
  let iter_exp iterator expr =
    f (fun () -> default_iterator.expr iterator expr) expr
  in
  { default_iterator with expr = iter_exp }

(* Bottom up. *)
let map_exprs f toplevel_phrases =
  apply_mapper_to_toplevel_phrases (expr_mapper f) toplevel_phrases

(* A thunk to iterate deeper is passed to f, so you can control iteration order. *)
(* Don't forget to call the thunk! *)
let iterate_exprs f toplevel_phrases =
  apply_iterator_to_toplevel_phrases (expr_iterator f) toplevel_phrases

(* Bottom up: f applied to leaves first. *)
let map_expr_by_id ~expr_id ~f toplevel_phrases =
  let replacer expr =
    if Ast_id.has_id expr_id ~expr
    then f expr
    else expr
  in
  map_exprs replacer toplevel_phrases

let replace_expr_by_id ~expr_id ~expr' toplevel_phrases =
  map_expr_by_id ~expr_id ~f:(fun _ -> expr') toplevel_phrases


module Exp = struct
  open Parsetree

  let var name =
    Ast_helper.Exp.ident ~loc:Location.none (longident_loced name)

  let string = Ast_helper.Exp.constant % Ast_helper.Const.string

  let rec list = function
    | [] ->
        Ast_helper.Exp.construct (longident_loced "[]") None
    | expr::rest ->
        Ast_helper.Exp.construct
          (longident_loced "::")
          (Some (Ast_helper.Exp.tuple [expr; list rest]))


  let of_string code =
    Lexing.from_string code
    |> Migrate_parsetree.Parse.expression Migrate_ast.selected_version
  
  let is_fun expr = match expr.pexp_desc with Pexp_fun _ -> true | _ -> false

  (* Bottom up. *)
  let map f expr =
    let mapper = expr_mapper f in
    mapper.expr mapper expr

  (* Don't forget to call the thunk: you control the iteration order. *)
  let iter f expr =
    let iterator = expr_iterator f in
    iterator.expr iterator expr

  let map_by_id ~expr_id ~f expr =
    let replacer expr =
      if Ast_id.has_id expr_id ~expr
      then f expr
      else expr
    in
    map replacer expr  

  let replace_by_id ~expr_id ~expr' expr =
    map_by_id ~expr_id ~f:(fun _ -> expr') expr  
end


module Pat = struct

  let var name =
    Ast_helper.Pat.var ~loc:Location.none (Location.mknoloc name)

  let get_var_name_opt (pattern : Parsetree.pattern) =
    match pattern.ppat_desc with
    | Parsetree.Ppat_var name_loced -> Some name_loced.txt
    | _                             -> None

  let rec all_var_names (pattern : Parsetree.pattern) : string list =
    let open Parsetree in
    match pattern.ppat_desc with
    | Ppat_any -> []
    | Ppat_var name_loced -> [name_loced.txt]
    | Ppat_alias (pat, name_loced) -> name_loced.txt :: all_var_names pat
    | Ppat_constant _ -> []
    | Ppat_interval (_, _) -> []
    | Ppat_tuple pats -> List.concat_map all_var_names pats
    | Ppat_construct (_, pat_opt) -> Option.to_list pat_opt |> List.concat_map all_var_names
    | Ppat_variant (_, pat_opt) -> Option.to_list pat_opt |> List.concat_map all_var_names
    | Ppat_record (fields, _) -> fields |> List.concat_map (fun (_, pat) -> all_var_names pat)
    | Ppat_array pats -> List.concat_map all_var_names pats
    | Ppat_or (l_pat, r_pat) -> all_var_names l_pat @ all_var_names r_pat
    | Ppat_constraint (pat, _) -> all_var_names pat
    | Ppat_type _ -> []
    | Ppat_lazy pat -> all_var_names pat
    | Ppat_unpack { txt = string_opt; _ } -> Option.to_list string_opt (* Module stuff, we'll count it.  *)
    | Ppat_exception pat -> all_var_names pat
    | Ppat_extension _ -> []
    | Ppat_open (_, pat) -> all_var_names pat

  end