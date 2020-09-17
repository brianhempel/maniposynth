open Ocamlformat_lib.Migrate_ast.Parsetree

(* Reminder: type structure = structure_item list *)

val structure_of_toplevel_phrases : toplevel_phrase list -> structure

val toplevel_phrases_of_structure : structure -> toplevel_phrase list

val apply_mapper_to_toplevel_phrases
  :  Ast_mapper.mapper
  -> toplevel_phrase list
  -> toplevel_phrase list

(* Bottom up: f applied to leaves first. *)
val map_expr_by_id
  :  expr_id:Ast_id.t
  -> f:(expression -> expression)
  -> toplevel_phrase list
  -> toplevel_phrase list

val replace_expr_by_id
  :  expr_id:Ast_id.t
  -> expr':expression
  -> toplevel_phrase list
  -> toplevel_phrase list

val longident : string -> Longident.t

val longident_loced : string -> Longident.t Location.loc

module Exp : sig
  val var    : string -> expression
  val string : string -> expression

  val of_string : string -> expression

  val is_fun : expression -> bool
end

module Pat : sig
  val get_var_name_opt : pattern -> string option
end

module Type : sig
  open Types

  (* Btype.fold_type_expr only applys f to the immediate children. *)
  val deep_fold_type_expr : ('a -> type_expr -> 'a) -> 'a -> type_expr -> 'a
end