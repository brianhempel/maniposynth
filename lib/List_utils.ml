open List

let last list = nth list (length list - 1)

let rec last_opt = function
  | []    -> None
  | [x]   -> Some x
  | _::xs -> last_opt xs

let pop_last_opt list =
  let last_opt = ref None in
  let rec pop_last_ = function
    | []    -> []
    | [x]   -> last_opt := Some x; []
    | x::xs -> x :: pop_last_ xs
  in
  let remaining = pop_last_ list in
  !last_opt
  |> Option.map (fun last -> (remaining, last))

let assoc_with_default target default list =
  match assoc_opt target list with
  | None       -> default
  | Some value -> value

let rec assoc3_opt target list =
  match list with
  | [] -> None
  | (key, v1, v2)::rest -> 
      if target == key
      then Some (v1, v2)
      else assoc3_opt target rest
