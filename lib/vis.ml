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

let rec exp_of_value Camlboot_interpreter.Data.{ v_; _ } =
  let open Camlboot_interpreter.Data in
  let open Ast_helper in
  let record_value_field_to_exp_field (name, v_ref) =
    (Loc.lident name, exp_of_value !v_ref)
  in
  match v_ with
  | Bomb | Hole _                         -> Shared.Ast.Exp.simple_var "??"
  | Int n                                 -> Exp.constant (Const.int n)
  | Int32 n                               -> Exp.constant (Const.int32 n)
  | Int64 n                               -> Exp.constant (Const.int64 n)
  | Nativeint n                           -> Exp.constant (Const.nativeint n)
  | Fun (arg_label, exp_opt, pat, exp, _) -> Exp.fun_ arg_label exp_opt pat exp
  | Function (cases, _)                   -> Exp.function_ cases
  | String bytes                          -> Exp.constant (Const.string (Bytes.to_string bytes))
  | Float n                               -> Exp.constant (Const.float (string_of_float n))
  | Tuple vs                              -> Exp.tuple (vs |>@ exp_of_value)
  | Constructor (ctor, _, v_opt)          -> Exp.construct (Loc.lident ctor) (v_opt |>& exp_of_value)
  | Prim _                                -> Shared.Ast.Exp.simple_var "??"
  | Fexpr _                               -> Shared.Ast.Exp.simple_var "??"
  | ModVal _                              -> Shared.Ast.Exp.simple_var "??"
  | InChannel _                           -> Shared.Ast.Exp.simple_var "??"
  | OutChannel _                          -> Shared.Ast.Exp.simple_var "??"
  | Record fields                         -> Exp.record (SMap.bindings fields |>@ record_value_field_to_exp_field) None
  | Lz _                                  -> Shared.Ast.Exp.simple_var "??"
  | Array vs                              -> Exp.array (vs |> Array.to_list |>@ exp_of_value)
  | Fun_with_extra_args (_, _, _)         -> Shared.Ast.Exp.simple_var "??"
  | Object _                              -> Shared.Ast.Exp.simple_var "??"
  | ExCall _                              -> Shared.Ast.Exp.simple_var "??"
  | ExDontCare                            -> Shared.Ast.Exp.simple_var "??"
