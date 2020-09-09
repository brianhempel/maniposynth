open Ocamlformat_lib.Migrate_ast.Parsetree
open Utils

type t = Location.t

let of_exp (exp : expression) : t =
    exp.pexp_loc

let string_of_id (id : t) : string =
  (formatter_to_stringifyer Location.print_loc) id

let id_string_of_exp = of_exp %> string_of_id
