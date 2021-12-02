type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let tree1 =
  Node (Empty, 0, Node (Node (Empty, 1, Empty), 0, Empty))
  [@@pos 608, 56]

let tree2 =
  Node (Node (Node (Empty, 1, Empty), 2, Empty), 3, Empty)
  [@@pos 1316, 73]

let tree3 = Node (Node (Empty, 1, Empty), 0, Empty) [@@pos 1950, 85]

let rec bstd_valid_ tree min_opt max_opt =
  match tree with
  | Empty -> true
  | Node ((l[@pos 7, 8]), (a[@pos 146, 4]), (r[@pos 289, 2])) -> (
      let l_is_valid = bstd_valid_ l min_opt (Some a) [@@pos 467, 7] in
      let r_is_valid = bstd_valid_ r (Some a) max_opt [@@pos 459, 103] in
      let children_valid = l_is_valid && r_is_valid [@@pos 730, 93] in
      match max_opt with
      | Some max -> (
          match min_opt with
          | Some min -> children_valid && a <= max && min <= a
          | None -> children_valid && a <= max )
      | None -> (
          match min_opt with
          | Some min -> children_valid && min <= a
          | None -> children_valid ) )
  [@@pos 177, 457]

let bstd_valid tree = bstd_valid_ tree None None [@@pos 1847, 543]

let () = assert (bstd_valid tree1 = false) [@@pos 652, 304]

let () = assert (bstd_valid tree2 = true) [@@pos 1323, 300]

let () = assert (bstd_valid tree3 = false) [@@pos 1970, 284]
