
(* let next counter_ref =
  incr counter_ref;
  !counter_ref *)

let clamp lo hi x =
  if hi < lo then
    raise (Invalid_argument "clamp high boundary must not be lower than the low boundary")
  else
    max lo (min hi x)


(* Many OCaml functions print imperatively to a formatter. Make them return a string instead. *)
(* Following https://github.com/ocaml/ocaml/blob/4.11/parsing/pprintast.ml string_of_expression *)
let formatter_to_stringifyer formatter =
  fun x ->
    ignore (Format.flush_str_formatter ());
    formatter Format.str_formatter x;
    Format.flush_str_formatter ()


(* Function composition and reverse compostion. *)
let (%)  f g = fun x -> f (g x)
let (%>) f g = fun x -> g (f x)
