open Parsetree
open Ast
open Util

type visualizer =
{ exp : Parsetree.expression
}

let exp_of_payload = function
  | PStr [{ pstr_desc = Pstr_eval (exp, _); _}] -> Some exp
  | _ -> None

let to_string { exp } = Exp.to_string exp

let add_vis_str_to_attrs vis_str (attrs : attribute list) =
  attrs @ [(Loc.mk "vis", PStr [Ast_helper.Str.eval (Exp.from_string vis_str)])]

let remove_vis_str_from_attrs vis_str (attrs : attribute list) =
  attrs |>@? begin fun ({ txt; _ }, payload) ->
    txt <> "vis" || (exp_of_payload payload |>& Exp.to_string) <> (Some vis_str)
  end

let all_from_attrs (attrs : attribute list) =
  attrs
  |>@@ begin function
    | ({ txt = "vis"; _}, payload) ->
      begin match exp_of_payload payload with
      | Some exp -> [{ exp = exp }]
      | None ->
        print_endline "[@vis] attribute payload should be an OCaml expression";
        []
      end
    | _ -> []
  end
