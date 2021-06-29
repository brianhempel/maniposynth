open Shared.Ast
open Shared.Util

include Map.Make(Loc)

(* Functions for when you have a list of items per loc. *)
let all_at_loc loc   map = find_opt loc map ||& []
let add_to_loc loc v map = add loc (v :: all_at_loc loc map) map
