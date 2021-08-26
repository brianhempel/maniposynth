open Shared.Ast
open Shared.Util

let suggestions =
  [ "fun x -> (??)"
  ]

let exclude_from_suggestions = ["Stdlib.__POS_OF__"; "Stdlib.__LOC_OF__"; "Stdlib.__LINE_OF__"]

(* Right now, possible visualizers are of type 'a -> 'b where 'a unifies with the type given. *)
let possible_functions_on_type typ type_env =
  let f _name path value_desc out =
    (* print_endline @@ name ^ "\t" ^ Path.name path ^ " : " ^ Type.to_string value_desc.Types.val_type; *) (* e.g. string_of_float Stdlib.string_of_float : float -> string *)
    match Type.flatten_arrows value_desc.Types.val_type with
    | [arg_type; _] ->
      begin try
        if Type.does_unify typ arg_type && not (List.mem (Path.name path) exclude_from_suggestions)
        then Exp.from_string (String.drop_prefix "Stdlib." (Path.name path)) :: out
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

