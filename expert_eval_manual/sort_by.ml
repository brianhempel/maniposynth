let rec insert_into_sorted f elem list =
  match list with
  | hd :: tail ->
      let insert_here = f elem <= f hd [@@pos 60, 0] in
      if insert_here then elem :: list else hd :: insert_into_sorted f elem tail
  | [] -> [ elem ]
  [@@pos 758, 88]

let rec sort_by f list =
  match list with
  | hd2 :: tail2 -> insert_into_sorted f hd2 (sort_by f tail2)
  | [] -> []
  [@@pos 754, 823]

let () =
  assert (sort_by (fun x -> -x) [ 1; 3; 2 ] = [ 3; 2; 1 ])
  [@@pos 1328, 881]

let () =
  assert (insert_into_sorted (fun x -> -x) 2 [ 3; 1 ] = [ 3; 2; 1 ])
  [@@pos 1375, 193]

let () =
  assert (insert_into_sorted (fun x -> -x) 2 [ 3; 3 ] = [ 3; 3; 2 ])
  [@@pos 1848, 324]
