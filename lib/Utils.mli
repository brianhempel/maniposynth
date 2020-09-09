
val clamp : 'a -> 'a -> 'a -> 'a

val string_of_file : string -> string
val save_file      : string -> string -> unit

val formatter_to_stringifyer : (Format.formatter -> 'a -> unit) -> 'a -> string

(* Function compostion and reverse compostion. These are the names in Batteries and Containers. *)
val (%)  : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val (%>) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c