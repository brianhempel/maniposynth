type nat = Z | S of nat

let rec plus a b =
  match b with S nat -> S (plus a nat) | Z -> a
  [@@pos 826, 273]

let plus_S = plus (S Z) (S (S (S Z))) [@@pos 1276, 283]
