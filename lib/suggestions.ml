open Shared.Ast
open Shared.Util
open Camlboot_interpreter

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


let rec flatten_value (value : Data.value) =
  let open Camlboot_interpreter.Data in
  let children =
    match value.v_ with
    | Bomb                                -> []
    | Hole _                              -> []
    | Int _                               -> []
    | Int32 _                             -> []
    | Int64 _                             -> []
    | Nativeint _                         -> []
    | Fun (_, _, _, _, _)                 -> []
    | Function (_, _)                     -> []
    | String _                            -> []
    | Float _                             -> []
    | Tuple vs                            -> vs
    | Constructor (_, _, None)            -> []
    | Constructor (_, _, Some v)          -> [v]
    | Prim _                              -> []
    | Fexpr _                             -> []
    | ModVal _                            -> []
    | InChannel _                         -> []
    | OutChannel _                        -> []
    | Record field_map                    -> SMap.values field_map |>@ (!)
    | Lz _                                -> []
    | Array v_arr                         -> Array.to_list v_arr
    | Fun_with_extra_args (v, vs, vs_map) -> v::vs @ (SMap.values vs_map |>@ snd)
    | Object { variables; _ }             -> SMap.values variables |>@ (!)
    | ExCall (v1, v2)                     -> [v1; v2]
    | ExDontCare                          -> []
  in
  value :: (children |>@@ flatten_value)


let suggestions (trace : Trace.t) (_type_lookups : Typing.lookups) (_parsed : program) frame_no value_ids_visible (_query : string) =
  let values_for_suggestion =
    let value_in_frame_by_id = Trace.entries_in_frame frame_no trace |>@ Trace.Entry.value |>@@ flatten_value |>@ (fun v -> (v.Data.id, v)) |> IntMap.of_list in
    value_ids_visible
    |>@& (fun v_id -> IntMap.find_opt v_id value_in_frame_by_id)
  in
  (* START HERE: FINALLY do something *)
  values_for_suggestion
  |>@ (fun v -> "(value_id " ^ string_of_int v.id ^ ")")
