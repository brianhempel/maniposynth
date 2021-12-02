type nat = Z | S of nat

let rec nat_max a b =
  match a with
  | S nat -> (
      match b with S (nat2[@pos 152, 5]) -> S (nat_max nat nat2) | Z -> a )
  | Z -> b
  [@@pos 841, 178]

let max_S = nat_max (S (S (S Z))) (S Z) [@@pos 1291, 188]

let max_S2 = nat_max (S Z) (S (S Z)) [@@pos 1772, 184]

let rec nat_list_max x1 =
  match x1 with
  | hd :: tail ->
      let rest_max = nat_list_max tail [@@pos 189, 20] in
      nat_max hd rest_max
  | [] -> Z
  [@@pos 1003, 773]

let nat_list = nat_list_max [ Z; S (S Z); S Z ] [@@pos 1453, 783]
