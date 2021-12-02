type nat = Z | S of nat

let rec plus a b =
  match b with S nat -> S (plus a nat) | Z -> a
  [@@pos 262, 79]

let plus_S = plus (S Z) (S (S (S Z))) [@@pos 794, 114]

let rec nat_mult a b =
  match b with S nat2 -> plus a (nat_mult a nat2) | Z -> Z
  [@@pos 1145, 330]

let nat_mult2 = nat_mult (S (S Z)) (S (S Z)) [@@pos 1595, 340]
