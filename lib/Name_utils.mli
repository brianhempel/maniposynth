
val longident       : string -> Longident.t
val longident_loced : string -> Longident.t Location.loc

val name_from_type : Types.type_expr -> string
