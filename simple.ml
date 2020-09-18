type nat = Z | S of nat

(* Ex: plus (S Z) (S (S (S Z))) *)
let rec plus a b =
  match a with
  | Z -> (
      ?? )
  | S nat1 ->
      let rec plus1 = plus nat1 b in
      ( ?? )

let current_ex = plus (S Z) (S (S (S Z)))
