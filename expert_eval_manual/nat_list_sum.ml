type nat = Z | S of nat

let rec plus a b =
  match b with S nat -> S (plus a nat) | Z -> a
  [@@pos 541, 74]

let plus_S = plus (S Z) (S (S (S Z))) [@@pos 1105, 94]

let rec nat_list_sum list =
  match list with
  | hd :: tail ->
      let sum_rest = nat_list_sum tail [@@pos 111, 6] in
      plus hd sum_rest
  | [] -> Z
  [@@pos 892, 614]

let nat_list = nat_list_sum [ S Z; S (S Z); S Z ] [@@pos 1342, 624]
