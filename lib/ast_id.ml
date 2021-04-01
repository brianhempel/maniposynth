(* Using parsing locations as id's. *)


  (* type position = Lexing.position =
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

let of_expr expr = expr.Parsetree.pexp_loc
let of_pat pat   = pat.Parsetree.ppat_loc
let of_loc loc   = loc

let string_of_t loc = Yojson.Safe.to_string (yojson_of_t loc)
let t_of_string str = t_of_yojson (Yojson.Safe.from_string str)

let has_id ?(expr) id =
  match expr with
  | Some e -> id = (of_expr e)
  | None   -> false *)