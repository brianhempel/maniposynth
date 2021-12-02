let rec contains target list =
  match list with
  | hd :: tail ->
      let hd_equals_target = hd = target [@@pos 488, 56] in
      hd_equals_target || contains target tail
  | [] -> false
  [@@pos 817, 270]

let contains2 = contains 2 [ 0; 2; 0 ] [@@pos 1267, 280]

let contains3 = contains 2 [ 1; 1; 1 ] [@@pos 1717, 275]
