let rec slice list i len =
  match list with
  | hd :: tail ->
      let result = slice tail (i - 1) len [@@pos 125, 12] in
      let rest_slice = slice tail 0 (len - 1) [@@pos 554, 48] in
      let result2 = hd :: rest_slice [@@pos 297, 106] in
      if i > 0 then result else if len > 0 then result2 else []
  | [] -> []
  [@@pos 791, 271]

let () = assert (slice [ 2; 3; 4; 5 ] 1 2 = [ 3; 4 ]) [@@pos 1241, 281]

let () = assert (slice [ 2; 3; 4; 5 ] 1 10 = [ 3; 4; 5 ]) [@@pos 1644, 286]

let () = assert (slice [ 2; 3; 4; 5 ] 5 2 = []) [@@pos 2042, 282]
