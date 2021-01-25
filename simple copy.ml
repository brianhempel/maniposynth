type nat = Z | S of nat

let rec nat_to_int = function
    | Z     -> 0
    | S nat -> 1 + nat_to_int nat

let rec plus a b =
  match a with
  | Z ->
      b
  | S nat1 ->
      let rec plus1 = plus nat1 b in
      S plus1

let current_ex = plus (S (S (S Z))) (S Z)

let main = print_endline (string_of_int (nat_to_int current_ex))
