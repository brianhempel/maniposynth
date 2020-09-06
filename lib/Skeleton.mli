open Ocamlformat_lib.Migrate_ast.Parsetree

type t =
  | Top_binding of value_binding * t
  | Constant of constant
  | Unknown
  | Labeled of expression (* var *)
  | Let of (value_binding * t) list * t
  | Fun of Asttypes.arg_label * expression option * pattern * t
  | Apply of expression * (Asttypes.arg_label * t) list
  | Construct of Longident.t * t option
  | Skels of t list

val show : t -> string

val skeletons_of_parsed_with_comments : toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments -> t list

(* val exp_to_skeleton : expression -> t *)
