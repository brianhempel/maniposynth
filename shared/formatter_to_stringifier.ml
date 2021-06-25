(* Many OCaml functions print imperatively to a formatter. Make them return a string instead. *)
(* Following https://github.com/ocaml/ocaml/blob/4.11/parsing/pprintast.ml string_of_expression *)
let f formatter =
  fun x ->
    ignore (Format.flush_str_formatter ());
    formatter Format.str_formatter x;
    Format.flush_str_formatter ()
