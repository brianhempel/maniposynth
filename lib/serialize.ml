

let to_string a =
  Marshal.to_string a [Closures]
  |> Base64.(encode_exn ~alphabet:uri_safe_alphabet)
  (* Marshal.to_bytes a [Closures]
  |> LZ4.Bytes.compress
  |> Bytes.to_string
  |> Base64.(encode_exn ~alphabet:uri_safe_alphabet) *)

let of_string str =
  let byte_str = Base64.(decode_exn ~alphabet:uri_safe_alphabet str) in
  Marshal.from_string byte_str 0
  (* str
  |> Base64.(decode_exn ~alphabet:uri_safe_alphabet)
  |> Bytes.of_string
  |> LZ4.Bytes.decompress ~length:10000000000
  |> (fun byte_str -> Marshal.from_bytes byte_str 0) *)


type value = Camlboot_interpreter.Data.value

let string_of_loc   : Location.t -> string     = to_string
let loc_of_string   : string     -> Location.t = of_string
let string_of_value : value      -> string     = to_string
let value_of_string : string     -> value      = of_string
