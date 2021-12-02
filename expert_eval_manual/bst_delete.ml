type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let tree1 =
  Node (Empty, 1, Node (Empty, 2, Node (Node (Empty, 3, Empty), 4, Empty)))

let tree2 =
  Node (Node (Node (Empty, 5, Empty), 5, Node (Empty, 6, Empty)), 7, Empty)
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
  [@@pos 1698, 19]

let rec bst_delete target elem =
  match elem with
  | Node (l, (a[@pos 349, 10]), (r[@pos 540, 15])) ->
      if target < a then Node (bst_delete target l, a, r)
      else if target > a then Node (l, a, bst_delete target r)
      else bst_delete target (btree_join l r)
  | Empty -> Empty
  [@@pos 0, 724]

let () =
  assert (bst_delete 5 tree2 = Node (Node (Empty, 6, Empty), 7, Empty))
  [@@pos 192, 431]

let () =
  assert (
    bst_delete 6 tree2 = Node (Node (Node (Empty, 5, Empty), 5, Empty), 7, Empty)
  )
  [@@pos 283, 532]
