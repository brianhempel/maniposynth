open Ocamlformat_lib.Migrate_ast.Parsetree

type value =
  | Ctor of string * string * value list (* name, type name, args *)
  | Failure of int (* frame_n *)

type tracesnap =
  | Tracesnap of int * string * value (* frame_n, id str, value *)

type trace = tracesnap list

val yojson_of_tracesnap : tracesnap -> Yojson.Safe.t

val add_tracepoint_placeholders : string -> toplevel_phrase list -> toplevel_phrase list

val fill_tracepoint_placeholders : Env.t -> Typedtree.structure -> toplevel_phrase list -> toplevel_phrase list

val run_with_tracing : string -> trace
