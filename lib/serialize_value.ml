

let string_of_value (v : Camlboot_interpreter.Data.value) =
  Serialize.to_string v

let value_of_string str : Camlboot_interpreter.Data.value =
  Serialize.of_string str
