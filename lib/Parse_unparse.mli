
type parsed = Parsetree.toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments

val parse_file : string -> parsed

val unparse : string -> parsed -> string
