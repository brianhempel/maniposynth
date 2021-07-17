(* Positioning elements on the canvas *)
open Parsetree
open Shared.Ast
open Shared.Util

type t = { x : int; y : int }

(* [@pos (100,200)] *)
let from_attrs attrs : t option =
  Attr.find_exp "pos" attrs
  |>&& begin function
  | { pexp_desc = Pexp_tuple [e1; e2]; _} ->
    begin match (Exp.int e1, Exp.int e2) with
    | (Some x, Some y) -> Some { x = x; y = y }
    | _ -> None
    end
  | _ -> None
  end
