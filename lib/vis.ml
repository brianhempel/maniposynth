open Parsetree
open Shared.Ast
open Shared.Util

type visualizer =
{ exp : Parsetree.expression
}

let to_string { exp } = Exp.to_string exp

let add_vis_str_to_attrs vis_str (attrs : attribute list) =
  Attr.add_exp "vis" (Exp.from_string vis_str) attrs

let remove_vis_str_from_attrs vis_str (attrs : attribute list) =
  Attr.remove_exp "vis" (Exp.from_string vis_str) attrs

let all_from_attrs (attrs : attribute list) =
  Attr.findall_exp "vis" attrs
  |>@ fun exp -> { exp = exp }
