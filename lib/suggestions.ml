open Shared.Ast
open Shared.Util
open Camlboot_interpreter

let exclude_from_suggestions = ["Stdlib.__POS_OF__"; "Stdlib.__LOC_OF__"; "Stdlib.__LINE_OF__"]

let modules_to_search = [None; Some (Longident.parse "Stdlib.List")]

let ctors_in_modules tenv mods =
  let f ({Types.cstr_res; _} as ctor_desc) out =
    (* let _ = cstr_arity in *)
    if Type.is_exn_type cstr_res then out else (* Exclude exceptions. *)
    ctor_desc :: out
  in
  mods |>@@ (fun module_lid_opt -> Env.fold_constructors f module_lid_opt tenv [])

let var_names_in_modules tenv mods =
  let f name path desc out =
    (* let target_is_var = Type.is_var_type typ in *)
    if Synth.is_imperative desc.Types.val_type then out else (* Don't use imperative functions *)
    if SSet.mem name Synth.unimplemented_prim_names then out else (* Interpreter doesn't implement some primitives *)
    if SSet.mem name Synth.dont_bother_names then out else
    String.drop_prefix "Stdlib." (Path.name path) :: out
  in
  mods |>@@ (fun module_lid_opt -> Env.fold_values f module_lid_opt tenv [])

let initial_ctor_names =
  ctors_in_modules Typing.initial_env modules_to_search
  |>@ (fun { Types.cstr_name; _ } -> cstr_name)
  |> SSet.of_list
let initial_var_names =
  var_names_in_modules Typing.initial_env modules_to_search
  |> SSet.of_list

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
  modules_to_search
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

let rec terminal_exps exp = (* Dual of gather_vbs *)
  let open Parsetree in
  match exp.pexp_desc with
  | Pexp_let (_, _, e)       -> terminal_exps e
  | Pexp_sequence (_, e2)    -> terminal_exps e2
  | Pexp_match (_, cases)    -> cases |>@ Case.rhs |>@@ terminal_exps
  | Pexp_letmodule (_, _, e) -> terminal_exps e
  | _                        -> [exp]


let options_for_value_id tenvs visible_values_in_frame selected_value_id =
  match visible_values_in_frame |> List.find_opt (fun (_v_str, v) -> v.Data.id = selected_value_id) with
  | Some (v_str, v) ->
    begin match v.Data.type_opt with
    | Some typ ->
      tenvs
      |>@@ possible_functions_on_type typ
      |> List.dedup
      |>@ Exp.to_string
      |>@ (fun code -> (code ^ " " ^ v_str, code ^ " value_id_" ^ string_of_int v.id))
      |> List.cons (v_str, "value_id_" ^ string_of_int v.id) (* include the value as an autocomplete option *)
    | _ ->
      []
    end
  | None ->
    []

(* KISS for now: lexical completions of last word typed *)
let suggestions (trace : Trace.t) (type_lookups : Typing.lookups) (final_tenv : Env.t) (prog : program) frame_no vbs_loc value_ids_visible value_strs ?selected_value_id (query : string) =
  let visible_values_in_frame =
    let value_in_frame_by_id = Trace.entries_in_frame frame_no trace |>@ Trace.Entry.value |>@@ flatten_value |>@ (fun v -> (v.Data.id, v)) |> IntMap.of_list in
    List.combine value_strs value_ids_visible
    |>@& (fun (v_str, v_id) -> IntMap.find_opt v_id value_in_frame_by_id |>& (fun v -> (v_str, v)))
    |> List.dedup_by snd
  in
  let locs = prog |> Exp.find_opt vbs_loc |>& terminal_exps ||& [] |>@ Exp.loc in
  let tenvs =
    (locs |>@& type_lookups.lookup_exp |>@ fun texp -> texp.Typedtree.exp_env)
    @ [final_tenv]
  in
  let options =
    match selected_value_id with
    | Some selected_value_id -> options_for_value_id tenvs visible_values_in_frame selected_value_id
    | _ ->
      let nonconstant_variableset =
        locs
        |>@ (fun loc -> Synth.nonconstant_names_at_loc loc prog)
        |> List.fold_left SSet.union SSet.empty
      in
      (* let tenv = type_lookups.lookup_exp vbs_loc |>& (fun texp -> texp.Typedtree.exp_env) ||& Env.empty in *)
      let ctorset =
        tenvs
        |>@@ (fun tenv -> ctors_in_modules tenv modules_to_search)
        |>@ (fun { Types.cstr_name; _ } -> cstr_name)
        |> SSet.of_list
        |> (fun s -> SSet.diff s initial_ctor_names)
      in
      let other_variableset =
        tenvs
        |>@@ (fun tenv -> var_names_in_modules tenv modules_to_search)
        |> SSet.of_list
        |> (fun s -> SSet.diff s initial_var_names)
      in
      let lexical_options =
        List.dedup @@
          SSet.elements nonconstant_variableset
          @ SSet.elements ctorset
          @ SSet.elements other_variableset
          @ SSet.elements initial_ctor_names
          @ SSet.elements initial_var_names
      in
      let subvalue_options =
        visible_values_in_frame
        |>@ begin fun (v_str, v) -> (v_str, "value_id_" ^ string_of_int v.id) end
      in
      subvalue_options
      @ (lexical_options |>@ fun code -> (code, code))
  in
  (* subvalue_options |>@ fst |> List.iter print_endline; *)
  begin match String.split " " query |> List.rev with
  | [] -> options |>@ snd
  | lastWord::restRev ->
    options
    |>@? (fun (shown_str, code) -> String.starts_with lastWord shown_str && lastWord <> code)
    |>@ begin fun (_, completion) ->
      completion::restRev |> List.rev |> String.concat " "
    end
  end

(* START HERE *)
(* It may be time to move on to a second example *)
(* Simple assert value? *)
(* "Use" in vis? *)
(* "Use" in pat? *)
(* Drag value into value? *)
