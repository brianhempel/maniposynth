

let clamp lo hi x =
  if hi < lo then
    raise (Invalid_argument "clamp high boundary must not be lower than the low boundary")
  else
    max lo (min hi x)

(* Jeffrey Scofield https://stackoverflow.com/a/53840784 *)
let string_of_file path =
  let in_chan = open_in_bin path in
  let str = really_input_string in_chan (in_channel_length in_chan) in
  close_in in_chan;
  str

let save_file path str =
  let out_chan = open_out path in
  output_string out_chan str;
  close_out out_chan


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
