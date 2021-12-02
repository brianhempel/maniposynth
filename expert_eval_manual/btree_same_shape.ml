type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let ex_tree =
  Node (Node (Empty, 0, Node (Empty, 0, Empty)), 0, Empty)
  [@@pos 820, 121]

let rec btree_same_shape tree1 tree2 =
  match tree1 with
  | Node (l1, _, r1) -> (
      match tree2 with
      | Node (l2, _, r2) ->
          let l_same = btree_same_shape l1 l2 [@@pos 108, 0] in
          let r_same = btree_same_shape r1 r2 [@@pos 477, 22] in
          l_same && r_same
      | Empty -> false )
  | Empty -> true
  [@@pos 541, 396]

let () =
  assert (btree_same_shape ex_tree (Node (Empty, 0, Empty)) = false)
  [@@pos 1927, 173]

let btree_same = btree_same_shape ex_tree ex_tree [@@pos 1430, 185]
