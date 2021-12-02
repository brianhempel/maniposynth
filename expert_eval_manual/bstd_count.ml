type 'a btree = Node of 'a btree * 'a * 'a btree | Empty

let rec bstd_count target tree =
  match tree with
  | Node ((l[@pos -6, 8]), (a[@pos 258, 12]), (r[@pos 344, 35])) ->
      let l_count =
        if target <= a then bstd_count target l else 0
        [@@pos 24, 158]
      in
      let r_count =
        if a <= target then bstd_count target r else 0
        [@@pos 106, 294]
      in
      let here_count = if a = target then 1 else 0 [@@pos 562, 202] in
      l_count + here_count + r_count
  | Empty -> 0
  [@@pos 1021, 383]

let tree1 =
  (Node (Node (Empty, -1, Node (Empty, 0, Empty)), 0, Empty)
  [@vis bstd_count 0])
  [@@pos 679, 85]

let () = assert (bstd_count 0 tree1 = 2) [@@pos 1548, 115]
