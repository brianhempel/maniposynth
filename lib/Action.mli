type t =
  | AddCodeToScopeBindings of string * string (* code str and scope id str *)
  | ReplaceCodeAtExpr of string * string (* code str and ast id str *)

val t_of_yojson : Yojson.Safe.t -> t
val yojson_of_t : t -> Yojson.Safe.t

val f : string -> t -> unit
