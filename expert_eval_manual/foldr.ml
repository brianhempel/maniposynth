let rec foldr f list acc =
  match list with
  | hd :: tail ->
      let acc' = foldr f tail acc [@@pos 153, -1] in
      f hd acc'
  | [] -> acc
  [@@pos 883, 255]

let () = assert (foldr List.cons [ 1; 2; 3 ] [] = [ 1; 2; 3 ]) [@@pos 1333, 265]
