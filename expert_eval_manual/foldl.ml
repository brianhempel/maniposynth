let rec foldl f acc list =
  match list with
  | (hd[@pos -4, -3]) :: tail ->
      let acc' = f acc hd [@@pos 79, 15] in
      foldl f acc' tail
  | [] -> acc
  [@@pos 842, 238]

let () =
  assert (foldl (fun acc x -> x :: acc) [] [ 1; 2; 3 ] = [ 3; 2; 1 ])
  [@@pos 1292, 248]
