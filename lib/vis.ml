open Parsetree
open Shared.Ast
open Shared.Util

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

let exclude_from_suggestions = ["Stdlib.__POS_OF__"; "Stdlib.__LOC_OF__"; "Stdlib.__LINE_OF__"]

(* Right now, possible visualizers are of type 'a -> 'b where 'a unifies with the type given. *)
let possible_vises_for_type typ type_env =
  let f _name path value_desc out =
    (* print_endline @@ name ^ "\t" ^ Path.name path ^ " : " ^ Type.to_string value_desc.Types.val_type; *) (* e.g. string_of_float Stdlib.string_of_float : float -> string *)
    match Type.flatten_arrows value_desc.Types.val_type with
    | [arg_type; _] ->
      begin try
        if Type.does_unify typ arg_type && not (List.mem (Path.name path) exclude_from_suggestions)
        then { exp = Exp.from_string @@ String.drop_prefix "Stdlib." (Path.name path) } :: out
        else out
      with _exn ->
        out
        (* Parse.expression fails to parse certain operators like Stdlib.~- *)
        (* begin match Location.error_of_exn exn with
        | Some (`Ok err) -> print_endline (Path.name path); Location.report_error Format.std_formatter err; out
        | _              -> out
        end *)
      end
    | _ -> out in
  let modules = [None; Some (Longident.parse "Stdlib.List")] in
  modules
  |>@@ fun module_lid_opt -> Env.fold_values f module_lid_opt type_env []
