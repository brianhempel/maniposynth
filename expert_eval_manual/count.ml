let rec count target list =
  match list with
  | hd :: tail ->
      let count3 = count target tail [@@pos 67, 12] in
      let if_then = if hd = target then 1 else 0 [@@pos 464, 29] in
      count3 + if_then
  | [] -> 0
  [@@pos 957, 224]

let count2 = count 3 [ 2; 3; 3; 5 ] [@@pos 1407, 234]
