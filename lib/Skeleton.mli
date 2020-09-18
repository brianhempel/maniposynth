open Ocamlformat_lib.Migrate_ast.Parsetree

type t =
  | Constant of expression

  | Unknown

  (* expr is the scope, the outermost expression (usually a let) *)
  | Bindings_rets of expression * binding_skel list * t list 

  | Fun of Asttypes.arg_label * expression option * pattern * t

  (* (apply_expr, fun_expr, arg_skels). can have 0 arguments, e.g. bare variable usage (var does not have have function type) *)
  | Apply of expression * expression * (Asttypes.arg_label * t) list 

  | Construct of expression * Longident.t * t option

and binding_skel = value_binding * t

val show : t -> string

val bindings_skels_of_parsed_with_comments
  :  toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments
  -> binding_skel list

(* val exp_to_skeleton : expression -> t *)
