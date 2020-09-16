type nat = Z | S of nat

(* type value =
  | Ctor of typ * string * value list
  | Int of int *)

(* Ex: plus (S Z) (S (S (S Z))) *)
let rec plus a b =
  let plus1 = plus a b in
  (* let () = failwith "hi" in *)
  (??)

(* Plan:
  1. Anything you do requires type information. Get the type information.
  2. Maybe recursive monomorphisation?
*)


(* match b with
   | Z -> a
   | S nat ->
       let
         plus1 = plus a nat
       in
       S plus1 *)
(* let one = (S Z) *)
(* let three = (S (S (S Z))) *)
let current_ex = plus (S Z) (S (S (S Z)))
(* let current_ex2 = List.map Fun.id [S Z; S (S (S Z))] *)