let rec snoc list elem =
  match list with
  | hd :: tail ->
      let rest_snoced = snoc tail elem [@@pos 58, 23] in
      hd :: rest_snoced
  | [] -> [ elem ]
  [@@pos 844, 305]

let () = assert (snoc [ 0; 0 ] 1 = [ 0; 0; 1 ]) [@@pos 1294, 315]
