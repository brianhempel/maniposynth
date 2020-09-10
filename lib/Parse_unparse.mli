
(* Comment-preserving parse/unparse using ocamlformat *)

type parsed = Parsetree.toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments

val parse_file_string : string -> parsed

val parse_file : string -> parsed

(* Wants pre-existing file name. *)
val unparse : string -> parsed -> string
