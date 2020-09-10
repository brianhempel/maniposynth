open List

let last list = nth list (length list - 1)

let last_opt = function
  | []   -> None
  | list -> Some (last list)


let assoc_with_default target default list =
  match assoc_opt target list with
  | None       -> default
  | Some value -> value
