type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let tree1 =
  Node (Node (Empty, -1, Node (Empty, 0, Empty)), 0, Empty)
  [@@pos 643, 75]

let tree2 =
  Node
    ( Node (Empty, -1, Node (Empty, 0, Empty)),
      0,
      Node (Empty, 1, Node (Empty, 20, Empty)) )
  [@@pos 1643, 63]

let rec bst_in_range tree lo hi =
  match tree with
  | Node (l, (a[@pos 288, 5]), (r[@pos 414, 3])) ->
      let r_in_range =
        if a <= hi then bst_in_range r a hi else []
        [@@pos 564, 147]
      in
      let l_in_range =
        if lo <= a then bst_in_range l lo a else []
        [@@pos 540, 9]
      in
      let here_in_range =
        if lo <= a && a <= hi then [ a ] else []
        [@@pos 136, 207]
      in
      l_in_range @ here_in_range @ r_in_range
  | Empty -> []
  [@@pos 389, 586]

let () = assert (bst_in_range tree1 0 0 = [ 0; 0 ]) [@@pos 659, 282]

let () = assert (bst_in_range tree1 (-10) 10 = [ -1; 0; 0 ]) [@@pos 1197, 301]

let () = assert (bst_in_range tree2 0 20 = [ 0; 0; 1; 20 ]) [@@pos 1745, 303]
