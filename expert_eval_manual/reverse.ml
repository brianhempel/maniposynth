let rec reverse list =
  match list with
  | hd :: tail ->
      let rev_rest = reverse tail [@@pos 29, 23] in
      rev_rest @ [ hd ]
  | [] -> []
  [@@pos 964, 365]

let reverse2 = reverse [ 1; 2; 3 ] [@@pos 1414, 375]
