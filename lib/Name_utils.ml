
let longident name =
  Option.get (Longident.unflatten [name])

let longident_loced name =
  Location.mknoloc (longident name)
  


let name_from_type typ =
  (Utils.formatter_to_stringifyer Printtyp.type_expr) typ
  |> String_utils.parameterize
  
  