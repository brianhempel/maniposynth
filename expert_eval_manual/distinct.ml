let rec contains target list =
  match list with
  | hd :: tail ->
      let hd_equals_target = hd = target [@@pos 488, 56] in
      hd_equals_target || contains target tail
  | [] -> false
  [@@pos 2, 62]

let rec distinct list =
  match list with
  | hd2 :: tail2 ->
      let rest_distinct = distinct tail2 [@@pos 97, 11] in
      let in_rest = contains hd2 tail2 [@@pos 441, 47] in
      (not in_rest) && rest_distinct
  | [] -> true
  [@@pos 1067, 155]

let distinct2 = distinct [ 0; 1; 2; 1 ] [@@pos 1517, 165]
