type 'a ltree = Node of 'a ltree * 'a ltree | Leaf of 'a

let rec ltree_fold f tree acc =
  match tree with
  | Node (l, r) ->
      let acc' = ltree_fold f r acc [@@pos 215, -5] in
      ltree_fold f l acc'
  | Leaf a -> f a acc
  [@@pos 902, 298]

let () =
  assert (
    ltree_fold List.cons (Node (Leaf 1, Node (Leaf 2, Leaf 3))) [] = [ 1; 2; 3 ]
  )
  [@@pos 1352, 308]
