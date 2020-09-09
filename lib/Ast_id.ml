open Ocamlformat_lib.Migrate_ast.Parsetree
open Utils

(* Using parsing locations as id's. *)

type t = Location.t =
  { loc_start : Lexing.position; loc_end : Lexing.position; loc_ghost : bool }

(* type Lexing.position = {
  	pos_fname : string;
  	pos_lnum : int;
  	pos_bol : int;
  	pos_cnum : int;
} *)

let of_exp (exp : expression) : t =
    exp.pexp_loc

let of_string (str : string) : t =
  Scanf.sscanf
    str
    "file '%s@' line %d line char %d file char %d to file '%s@' line %d line char %d file char %d"
    (fun start_fname start_lnum start_bol start_cnum end_fname end_lnum end_bol end_cnum->
      { loc_start =
          { pos_fname = start_fname
          ; pos_lnum  = start_lnum
          ; pos_bol   = start_bol
          ; pos_cnum  = start_cnum
          }
      ; loc_end =
          { pos_fname = end_fname
          ; pos_lnum  = end_lnum
          ; pos_bol   = end_bol
          ; pos_cnum  = end_cnum
          }
      ; loc_ghost =
          false
      }
    )

let string_of_id (id : t) : string =
  Printf.sprintf
    "file '%s' line %d line char %d file char %d to file '%s' line %d line char %d file char %d"
    id.loc_start.pos_fname
    id.loc_start.pos_lnum
    id.loc_start.pos_bol
    id.loc_start.pos_cnum
    id.loc_end.pos_fname
    id.loc_end.pos_lnum
    id.loc_end.pos_bol
    id.loc_end.pos_cnum

let id_string_of_exp = of_exp %> string_of_id
