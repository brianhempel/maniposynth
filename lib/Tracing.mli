open Ocamlformat_lib.Migrate_ast.Parsetree

val add_tracepoint_placeholders : string -> toplevel_phrase list -> toplevel_phrase list

val fill_tracepoint_placeholders : Env.t -> Typedtree.structure -> toplevel_phrase list -> toplevel_phrase list
