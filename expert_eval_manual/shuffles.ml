let rec shuffles list1 list2 =
  match list1 with
  | hd1 :: tail1 -> (
      let rest1 = shuffles tail1 list2 [@@pos 61, 10] in
      let results1 = List.map (List.cons hd1) rest1 [@@pos 33, 160] in
      match list2 with
      | hd2 :: tail2 ->
          let rest2 = shuffles list1 tail2 [@@pos 165, 103] in
          let results2 = List.map (List.cons hd2) rest2 [@@pos 516, 256] in
          results1 @ results2
      | [] -> List.map (List.cons hd1) rest1 )
  | [] -> ( match list2 with hd2 :: tail2 -> [ list2 ] | [] -> [ [] ] )
  [@@pos 449, 168]

let shuffles2 = shuffles [ 1; 3 ] [ 2; 4 ] [@@pos 1437, 184]
