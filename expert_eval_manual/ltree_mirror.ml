type 'a ltree = Node of 'a ltree * 'a ltree | Leaf of 'a

let rec ltree_mirror x1 =
  match x1 with
  | Node (l, r) -> Node (ltree_mirror r, ltree_mirror l)
  | Leaf a -> x1
  [@@pos 829, 362]

let () =
  assert (
    ltree_mirror (Node (Leaf 1, Node (Leaf 2, Leaf 3)))
    = Node (Node (Leaf 3, Leaf 2), Leaf 1) )
  [@@pos 1279, 372]
