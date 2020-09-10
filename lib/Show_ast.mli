open Ocamlformat_lib.Migrate_ast.Parsetree

val dummy_expr : expression

val pat      : pattern    -> string
val expr     : expression -> string
val constant : constant   -> string

val longident : Longident.t -> string

val fun_param : Asttypes.arg_label -> expression option -> pattern -> string
val app_arg   : Asttypes.arg_label -> expression -> string
