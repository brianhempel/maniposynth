open Ocamlformat_lib.Migrate_ast.Parsetree

type branch_path = int list

type t =
  | Constant of branch_path * expression

  | Unknown

  (* expr is the scope, the outermost expression (usually a let) *)
  | Bindings_rets of expression * binding_skel list * t list 

  | Fun of branch_path * Asttypes.arg_label * expression option * pattern * t

  (* (apply_expr, fun_expr, arg_skels). can have 0 arguments, e.g. bare variable usage (var does not have have function type) *)
  | Apply of branch_path * expression * expression * (Asttypes.arg_label * t) list 

  | Construct of branch_path * expression * Longident.t * t option

and binding_skel = branch_path * value_binding * t

val string_of_branch_path : branch_path -> string
val branch_path_of_string : string -> branch_path

val show : t -> string

val bindings_skels_of_parsed_with_comments
  :  toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments
  -> binding_skel list

val destruction_renamings_of_expr : expression -> (string * string) list

val apply_renamings : (string * string) list -> expression -> expression

(* val exp_to_skeleton : expression -> t *)
