let rec fold f list acc =
  match list with
  | hd :: tail ->
      let acc' = f hd acc [@@pos 158, 121] in
      let fold_rest = fold f tail acc' [@@pos 106, 5] in
      fold_rest
  | [] -> acc
  [@@pos 1022, 329]

let fold_List = fold List.cons [ 1; 2; 3 ] [] [@@pos 1472, 339]
