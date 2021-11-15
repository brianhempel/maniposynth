open Ast
open Util

include MapPlus(Loc)

(* Functions for when you have a list of items per loc. *)
let all_at_loc loc   map = find_opt loc map ||& []
let add_to_loc loc v map = add loc (v :: all_at_loc loc map) map
let add_all_to_loc loc v map = add loc (v @ all_at_loc loc map) map
