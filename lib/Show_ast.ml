open Ocamlformat_lib.Migrate_ast.Parsetree

let dummy_expr : expression =
  { pexp_desc       = Pexp_unreachable
  ; pexp_loc        = Location.none
  ; pexp_loc_stack  = []
  ; pexp_attributes = []
  }

(* let unknown_pat : pattern =
  { ppat_desc       = Ppat_var (Location.mknoloc "?")
  ; ppat_loc        = Location.none
  ; ppat_loc_stack  = []
  ; ppat_attributes = []
  }
 *)

let pat pat = (Utils.formatter_to_stringifyer Pprintast.pattern) pat

let expr = Pprintast.string_of_expression

let constant constant = expr { dummy_expr with pexp_desc = Pexp_constant constant }

let longident longident = (Utils.formatter_to_stringifyer Pprintast.longident) longident

(* Pprintast doesn't expose its arg_label function...or does it! *)
let fun_param param_label default_opt pat =
  let dummy_fun = { dummy_expr with pexp_desc = Pexp_fun (param_label, default_opt, pat, dummy_expr) } in
  let fun_str = expr dummy_fun in (* "fun x -> " *)
  (* Cut off "fun " from the front *)
  let fun_str = String.sub fun_str 4 (String.length fun_str - 4) in (* "x -> " *)
  (* Cut off " -> " from the back *)
  String.sub fun_str 0 (String.rindex fun_str '-' - 1)

(* Pprintast doesn't expose its label_x_expression_param function...or does it! *)
let app_arg arg_label arg_expr =
  let dummy_var = { dummy_expr with pexp_desc = Pexp_ident (Location.mknoloc (Longident.Lident "f")) } in
  let dummy_app = { dummy_expr with pexp_desc = Pexp_apply (dummy_var, [(arg_label, arg_expr)]) } in
  let app_str = expr dummy_app in
  String.sub app_str 2 (String.length app_str - 2)
