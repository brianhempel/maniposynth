type 'a ltree = Node of 'a ltree * 'a ltree | Leaf of 'a

let rec ltree_inorder tree =
  match tree with
  | Node (l, r) ->
      let inorder_l = ltree_inorder l [@@pos 58, 21] in
      let inorder_r = ltree_inorder r [@@pos 412, 136] in
      inorder_l @ inorder_r
  | Leaf a -> [ a ]
  [@@pos 873, 261]

let () =
  assert (ltree_inorder (Node (Leaf 1, Node (Leaf 2, Leaf 3))) = [ 1; 2; 3 ])
  [@@pos 1323, 271]
