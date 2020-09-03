open Ocamlformat_lib.Migrate_ast.Parsetree

type t =
  | Constant of constant
  | Unknown
  | Let of (value_binding * t) list * t
  | Fun of Asttypes.arg_label * expression option * pattern * t
  | App of t * (Asttypes.arg_label * expression option * pattern) * (Asttypes.arg_label * expression * t) * t

val show : t -> string

val skeletons_of_parsed_with_comments : toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments -> t list

(* val exp_to_skeleton : expression -> t *)
