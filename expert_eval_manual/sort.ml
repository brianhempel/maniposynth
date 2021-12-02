let rec insert_into_sorted elem list =
  match list with
  | hd :: tail ->
      if elem <= hd then elem :: list else hd :: insert_into_sorted elem tail
  | [] -> [ elem ]
  [@@pos 429, 108]

let rec sort list =
  match list with
  | hd2 :: tail2 ->
      let tail_sorted = sort tail2 [@@pos 117, 5] in
      insert_into_sorted hd2 tail_sorted
  | [] -> []
  [@@pos 258, 671]

let () = assert (sort [ 2; 3; 1 ] = [ 1; 2; 3 ]) [@@pos 977, 746]

let () = assert (insert_into_sorted 2 [ 1; 3 ] = [ 1; 2; 3 ]) [@@pos 1453, 123]

let () = assert (insert_into_sorted 3 [ 1 ] = [ 1; 3 ]) [@@pos 1894, 114]
