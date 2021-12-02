type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let ex_tree1 =
  Node (Node (Empty, 1, Node (Empty, 2, Empty)), 3, Empty)
  [@@pos 925, 280]

let rec bst_contains target (tree[@vis r]) =
  match tree with
  | Node (l, a, r) ->
      a = target
      || if target < a then bst_contains target l else bst_contains target r
  | Empty -> false
  [@@pos 254, 482]

let () = assert (bst_contains 2 ex_tree1 = true) [@@pos 1227, 550]

let () = assert (bst_contains 4 ex_tree1 = false) [@@pos 1657, 554]

let () = assert (bst_contains 0 ex_tree1 = false) [@@pos 2108, 575]
