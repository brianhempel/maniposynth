type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let rec btree_enum height =
  let treeses smallers =
    let fun_l l =
      let fun_r r = Node (l, (), r) [@@pos -2, 17] in
      List.map fun_r smallers
      [@@pos -14, 23]
    in
    List.map fun_l smallers
    [@@pos 33, 216]
  in
  if height <= 0 then [ Empty ]
  else Empty :: List.concat (treeses (btree_enum (height - 1)))
  [@@pos 78, 533]

let () = assert (btree_enum 0 = [ Empty ]) [@@pos 1241, 119]

let () =
  assert (btree_enum 1 = [ Empty; Node (Empty, (), Empty) ])
  [@@pos 1551, 118]

let () =
  assert (
    btree_enum 2
    = [
        Empty;
        Node (Empty, (), Empty);
        Node (Empty, (), Node (Empty, (), Empty));
        Node (Node (Empty, (), Empty), (), Empty);
        Node (Node (Empty, (), Empty), (), Node (Empty, (), Empty));
      ] )
  [@@pos 878, 239]
