type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let tree1 =
  Node (Empty, 1, Node (Empty, 2, Node (Node (Empty, 3, Empty), 4, Empty)))

let tree2 =
  Node (Node (Empty, 5, Node (Empty, 6, Empty)), 7, Empty)
  [@@pos 745, 61]

let rec btree_join tree1 tree2 =
  match tree1 with
  | Node ((l[@pos 90, 24]), (a[@pos 368, 17]), (r[@pos 601, 4])) -> (
      let r_join = btree_join r tree2 [@@pos 1010, 115] in
      match r with
      | Empty -> Node (l, a, tree2)
      | Node ((r_l[@pos 437, 115]), (r_a[@pos 646, 124]), (r_r[@pos 778, 108]))
        -> (
          match r_join with
          | Node (join_l, join_a, join_r) ->
              Node (Node (l, a, join_l), join_a, join_r)
          | Empty -> failwith "impossible" ) )
  | Empty -> tree2
  [@@pos 131, 483]

let () =
  assert (
    btree_join tree1 tree2
    = Node
        ( Node (Empty, 1, Node (Empty, 2, Node (Empty, 3, Empty))),
          4,
          Node (Node (Empty, 5, Node (Empty, 6, Empty)), 7, Empty) ) )
  [@@pos 1345, 177]

let () =
  assert (
    btree_join tree1 Empty
    = Node (Node (Empty, 1, Node (Empty, 2, Node (Empty, 3, Empty))), 4, Empty)
  )
  [@@pos 1358, 280]
