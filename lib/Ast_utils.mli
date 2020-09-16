open Ocamlformat_lib.Migrate_ast.Parsetree

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

val parse_expr : string -> expression

val longident : string -> Longident.t

val longident_loced : string -> Longident.t Location.loc

module Exp : sig
  val var : string -> expression
end
