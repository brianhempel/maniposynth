open Ocamlformat_lib.Migrate_ast.Parsetree

(* Keep these abstract so we can change them later. *)
type t

val of_expr : expression -> t

val t_of_yojson : Yojson.Safe.t -> t
val yojson_of_t : t -> Yojson.Safe.t

val has_id : ?expr:expression -> t -> bool
