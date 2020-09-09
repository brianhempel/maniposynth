(* Keep these abstract so we can change them later. *)

type t

val id_string_of_exp : Ocamlformat_lib.Migrate_ast.Parsetree.expression -> string

val of_string : string -> t
