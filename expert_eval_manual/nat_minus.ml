type nat = Z | S of nat

let rec nat_minus a b =
  match a with
  | S nat -> ( match b with S nat2 -> nat_minus nat nat2 | Z -> a )
  | Z -> Z
  [@@pos 688, 139]

let nat_minus2 = nat_minus (S (S (S Z))) (S (S Z)) [@@pos 1138, 149]

let nat_minus3 = nat_minus (S Z) (S (S Z)) [@@pos 1370, 334]
