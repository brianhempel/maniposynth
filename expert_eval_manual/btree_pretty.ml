type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

type 'a tchar = N of 'a | L

let ex_tree =
  Node (Node (Empty, 1, Node (Empty, 2, Empty)), 3, Empty)
  [@@pos 856, 81]

let rec btree_pretty tree =
  match tree with
  | Node (a_btree, a, a_btree2) ->
      (N a :: btree_pretty a_btree) @ btree_pretty a_btree2
  | Empty -> [ L ]
  [@@pos 902, 250]

let () =
  assert (btree_pretty ex_tree = [ N 3; N 1; L; N 2; L; L; L ])
  [@@pos 1712, 227]
