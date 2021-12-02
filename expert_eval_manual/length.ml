let rec length list =
  match list with hd :: tail -> 1 + length tail | [] -> 0
  [@@pos 995, 236]

let length2 = length [ 0; 0; 0 ] [@@pos 1445, 246]
