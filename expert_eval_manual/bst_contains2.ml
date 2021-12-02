type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let ex_btree =
  Node (Node (Empty, 1, Node (Empty, 2, Empty)), 3, Empty)
  [@@pos 930, 122]

let rec bst_contains2 tree would_be_equal target =
  match tree with
  | Node (l, a, r) ->
      if target < a then bst_contains2 l would_be_equal target
      else bst_contains2 r (Some a) target
  | Empty -> (
      match would_be_equal with Some a2 -> a2 = target | None -> false )
  [@@pos 192, 364]

let () = assert (bst_contains2 ex_btree None 2 = true) [@@pos 1679, 534]

let () = assert (bst_contains2 ex_btree None 0 = false) [@@pos 1734, 359]

let () = assert (bst_contains2 ex_btree None 4 = false) [@@pos 2296, 354]

let () = assert (bst_contains2 ex_btree None 1 = true) [@@pos 1756, 396]

let () = assert (bst_contains2 ex_btree None 3 = true) [@@pos 2308, 577]
