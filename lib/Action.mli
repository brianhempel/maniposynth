type t =
  | AddCodeToScopeBindings of string * string (* code str and scope id str *)
  | ReplaceCodeAtExpr of string * string (* code str and ast id str *)
  | DestructAndReplaceCodeAtExpr of string * string (* destruct path str and ast id str *)

type destruction =
  { type_str  : string
  ; ctor_name : string
  ; arg_n     : int
  }

type destruct_path = (string * destruction list) (* scrutinee_code, destructions *)

val t_of_yojson : Yojson.Safe.t -> t
val yojson_of_t : t -> Yojson.Safe.t

val destruct_path_of_string : string -> destruct_path
val string_of_destruct_path : destruct_path -> string

val f : string -> t -> unit
