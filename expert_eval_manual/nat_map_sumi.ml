type nat = Z | S of nat

let rec plus a b =
  match b with S nat -> S (plus a nat) | Z -> a
  [@@pos 580, 28]

let plus_S = plus (S Z) (S (S (S Z))) [@@pos 1087, 56]

let rec nat_map_sumi f i =
  let i_result = f i [@@pos 58, 20] in
  match i with S nat2 -> plus i_result (nat_map_sumi f nat2) | Z -> i_result
  [@@pos 993, 404]

let nat_map = nat_map_sumi (fun x -> plus (S Z) x) (S (S Z)) [@@pos 1443, 414]
