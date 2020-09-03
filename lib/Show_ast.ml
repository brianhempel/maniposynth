open Ocamlformat_lib.Migrate_ast.Parsetree

let dummy_exp : expression =
  { pexp_desc       = Pexp_unreachable
  ; pexp_loc        = Location.none
  ; pexp_loc_stack  = []
  ; pexp_attributes = []
  }

(* Following https://github.com/ocaml/ocaml/blob/4.11/parsing/pprintast.ml string_of_expression *)
let pat pat =
    ignore (Format.flush_str_formatter ());
    Pprintast.pattern Format.str_formatter pat;
    Format.flush_str_formatter ()

let exp = Pprintast.string_of_expression

let constant constant = exp { dummy_exp with pexp_desc = Pexp_constant constant }

(* Pprintast doesn't expose its arg_label function...or does it! *)
let fun_param param_label default_opt pat =
  let dummy_fun = { dummy_exp with pexp_desc = Pexp_fun (param_label, default_opt, pat, dummy_exp) } in
  let fun_str = exp dummy_fun in (* "fun x -> " *)
  (* Cut off "fun " from the front *)
  let fun_str = String.sub fun_str 4 (String.length fun_str - 4) in (* "x -> " *)
  (* Cut off " -> " from the back *)
  String.sub fun_str 0 (String.rindex fun_str '-' - 1)

(* Pprintast doesn't expose its label_x_expression_param function...or does it! *)
let app_arg arg_label arg_exp =
  let dummy_var = { dummy_exp with pexp_desc = Pexp_ident (Location.mknoloc (Longident.Lident "f")) } in
  let dummy_app = { dummy_exp with pexp_desc = Pexp_apply (dummy_var, [(arg_label, arg_exp)]) } in
  let app_str = exp dummy_app in
  String.sub app_str 2 (String.length app_str - 2)
