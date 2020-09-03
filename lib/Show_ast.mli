open Ocamlformat_lib.Migrate_ast.Parsetree

val dummy_exp : expression

val pat      : pattern    -> string
val exp      : expression -> string
val constant : constant   -> string

val fun_param : Asttypes.arg_label -> expression option -> pattern -> string
val app_arg   : Asttypes.arg_label -> expression -> string
