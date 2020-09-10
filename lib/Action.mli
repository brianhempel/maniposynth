type t =
  | AddCodeToScopeBindings of string * Ast_id.t
  | ReplaceCodeAtExpr of string * Ast_id.t

val t_of_yojson : Yojson.Safe.t -> t
val yojson_of_t : t -> Yojson.Safe.t

val f : string -> t -> unit
