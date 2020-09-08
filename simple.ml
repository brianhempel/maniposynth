

type nat = Z
         | S of nat

(* Ex: plus (S Z) (S (S (S Z))) *)
let rec plus a b =
  let g = 3 + 4 in
  ( ?? )
  (* match b with
  | Z -> a
  | S nat ->
      let
        plus1 = plus a nat
      in
      S plus1 *)

and seven = 7