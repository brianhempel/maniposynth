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

let set_pos_attr x y attrs : attributes =
  let pos_exp = Exp.tuple [Exp.int_lit x; Exp.int_lit y] in
  Attr.set_exp "pos" pos_exp attrs

let pos_attrs attrs : attributes =
  Attr.findall "pos" attrs

let remove_pos_attr attrs : attributes =
  Attr.remove_name "pos" attrs

let set_vb_pos  x y vb  = { vb  with pvb_attributes  = set_pos_attr x y vb.pvb_attributes }
let set_exp_pos x y exp = { exp with pexp_attributes = set_pos_attr x y exp.pexp_attributes }

let remove_exp_pos exp = { exp with pexp_attributes = remove_pos_attr exp.pexp_attributes }

let exp_pos_attrs exp = pos_attrs exp.pexp_attributes