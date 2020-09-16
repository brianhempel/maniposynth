
val last         : 'a list -> 'a
val last_opt     : 'a list -> 'a option
val pop_last_opt : 'a list -> ('a list * 'a) option

val assoc_with_default : 'a -> 'b -> ('a * 'b) list -> 'b
val assoc3_opt         : 'a -> ('a * 'b * 'c) list -> ('b * 'c) option
