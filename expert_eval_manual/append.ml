let rec append list1 list2 =
  match list1 with
  | hd :: tail ->
      let append_rest = append tail list2 [@@pos 188, 29] in
      hd :: append_rest
  | [] -> list2
  [@@pos 730, 241]

let () = assert (append [ 1; 2 ] [ 3; 4 ] = [ 1; 2; 3; 4 ]) [@@pos 1180, 251]
