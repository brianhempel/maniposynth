

let to_string ?(failure_location_str = "") a =
  begin try Marshal.to_string a [Closures]
  with Invalid_argument msg ->
    print_endline @@ "Serialization failure (" ^ failure_location_str ^ "): " ^ msg;
    ""
  end
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


type value  = Camlboot_interpreter.Data.value
type vtrace = Camlboot_interpreter.Data.vtrace

let string_of_loc   : Location.t -> string = to_string
let loc_of_string   : string -> Location.t = of_string
let string_of_value : ?failure_location_str:string -> value -> string = to_string
let value_of_string : string -> value = of_string
let string_of_vtrace : vtrace -> string = to_string
let vtrace_of_string : string -> vtrace = of_string
