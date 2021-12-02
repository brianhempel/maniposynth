type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let rec bstd_insert elem tree =
  match tree with
  | Node ((l[@pos 32, -9]), (a[@pos 355, 6]), (r[@pos 545, -6])) ->
      if elem <= a then Node (bstd_insert elem l, a, r)
      else Node (l, a, bstd_insert elem r)
  | Empty -> Node (Empty, elem, Empty)
  [@@pos 870, 536]

let () = assert (bstd_insert 0 Empty = Node (Empty, 0, Empty)) [@@pos 76, 80]

let ex_tree =
  Node (Node (Empty, 0, Node (Empty, 10, Empty)), 20, Empty)
  [@@pos 557, 99]

let () =
  assert (
    bstd_insert 5 ex_tree
    = Node (Node (Empty, 0, Node (Node (Empty, 5, Empty), 10, Empty)), 20, Empty)
  )
  [@@pos 1315, 102]
