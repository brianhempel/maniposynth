let rec quickselect list nth =
  match list with
  | pivot :: tail ->
      let smaller = List.filter (fun x -> x <= pivot) tail [@@pos -12, 112] in
      let smaller_len = List.length smaller [@@pos 37, 238] in
      let nth_right = nth - smaller_len - 1 [@@pos 77, 329] in
      let larger = List.filter (fun x -> x > pivot) tail [@@pos 354, 119] in
      if nth <= smaller_len then quickselect smaller nth
      else if nth_right <= 0 then pivot
      else quickselect larger nth_right
  | [] -> failwith "out of bounds"
  [@@pos 951, 298]

let () = assert (quickselect [ 30; 40; 20; 50; 10 ] 4 = 40) [@@pos 1893, 326]
