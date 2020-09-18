open Ocamlformat_lib.Migrate_ast.Parsetree

(* Reminder: type Parsetree.structure = structure_item list *)

val structure_of_toplevel_phrases : toplevel_phrase list -> structure

val toplevel_phrases_of_structure : structure -> toplevel_phrase list

val apply_mapper_to_toplevel_phrases
  :  Ast_mapper.mapper
  -> toplevel_phrase list
  -> toplevel_phrase list

val apply_iterator_to_toplevel_phrases
  :  Ast_iterator.iterator
  -> toplevel_phrase list
  -> unit

val map_exprs
  :  (expression -> expression)
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
  val list   : expression list -> expression

  val of_string : string -> expression

  val is_fun : expression -> bool
end

module Pat : sig
  val var : string -> pattern

  val get_var_name_opt : pattern -> string option
end
