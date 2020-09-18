(* For all these functions, the main (larger) string is the first non-optional input. *)

val safe_sub : string -> int -> int -> string

val prefix : string -> int -> string
val suffix : string -> int -> string
val drop   : string -> int -> string

val starts_with : string -> String.t -> bool
val ends_with : string -> String.t -> bool

val find_index : ?start_index:int -> string -> string -> int option

val split : ?limit:int -> ?start_index:int -> string -> string -> string list

val replace : string -> target:string -> replacement:string -> string

(* "a b-c d'" => "a_b_c_d_" *)
val parameterize : string -> string
