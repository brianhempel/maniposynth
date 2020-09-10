open Ocamlformat_lib.Migrate_ast.Parsetree

(* Using parsing locations as id's. *)

type position = Lexing.position =
  { pos_fname : string
  ; pos_lnum  : int
  ; pos_bol   : int
  ; pos_cnum  : int
  } [@@deriving yojson]

type t = Location.t =
  { loc_start : position
  ; loc_end   : position
  ; loc_ghost : bool
  } [@@deriving yojson]


let of_expr expr = expr.pexp_loc
let of_pat pat   = pat.ppat_loc

let has_id ?(expr) id =
  match expr with
  | Some e -> id = (of_expr e)
  | None   -> false