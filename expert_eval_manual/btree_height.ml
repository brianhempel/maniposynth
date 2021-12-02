type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let rec btree_height tree =
  match tree with
  | Node (l, _, r) ->
      let l_height = btree_height l [@@pos 45, 0] in
      let r_height = btree_height r [@@pos 447, 10] in
      let child_max = max l_height r_height [@@pos 371, 168] in
      1 + child_max
  | Empty -> 0
  [@@pos 574, 256]

let () =
  assert (
    btree_height (Node (Node (Empty, 0, Node (Empty, 0, Empty)), 0, Empty)) = 3
  )
  [@@pos 911, 99]
