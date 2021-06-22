open Parsetree
open Ast
open Util

type visualizer =
{ typ : Types.type_expr
; exp : Parsetree.expression
}

(* string_of_cst and string_of_payload are copied from OCaml's builtin_attributes.ml *)
(* (they aren't exposed) *)
let string_of_const = function
  | Pconst_string(str, _) -> Some str
  | _ -> None
let string_of_payload = function
  | PStr [{ pstr_desc = Pstr_eval ({pexp_desc = Pexp_constant cst; _}, _); _}] -> string_of_const cst
  | _ -> None

let to_string { typ; exp } = Type.to_string typ ^ " => " ^ Exp.to_string exp

let add_vis_str_to_attrs vis_str (attrs : attribute list) =
  attrs @ [(Loc.mk "vis", PStr [Ast_helper.Str.eval (Exp.string_lit vis_str)])]

let remove_vis_str_from_attrs vis_str (attrs : attribute list) =
  attrs |>@? begin fun ({ txt; _ }, payload) ->
    txt <> "vis" || string_of_payload payload <> (Some vis_str)
  end

let all_from_attrs type_env (attrs : attribute list) =
  attrs
  |>@@ begin function
    | ({ txt = "vis"; _}, payload) ->
      begin match string_of_payload payload with
      | Some str ->
        (* e.g. "'a list => length" *)
        begin match String.split ~limit:2 "=>" str with
        | [type_str; f_str] ->
          begin try
            [{ typ = Type.from_string ~env:type_env type_str; exp = Exp.from_string f_str }]
          with
          | Typetexp.Error (_, type_env, error) -> Typetexp.report_error type_env Format.std_formatter error; []
          end
        | _ ->
          print_endline "[@vis] string should look like e.g. \"'a list => length\"";
          []
        end
      | None ->
        print_endline "[@vis] attribute payload should be a quoted string";
        []
      end
    | _ -> []
  end
