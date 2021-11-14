(* For making a lookup table of the expression types of a program. *)

open Shared
open Shared.Ast
open Shared.Util

type lookups =
  { lookup_exp : Location.t -> Typedtree.expression option
  ; lookup_pat : Location.t -> Typedtree.pattern option
  }

let empty_lookups =
  { lookup_exp = (fun _ -> None)
  ; lookup_pat = (fun _ -> None)
  }

let formatter = Format.std_formatter

let initial_env =
  (* Need to add (??) to the Stdlib typing environment *)
  let fake_filename = "type_prelude.ml" in
  let buf = Lexing.from_string
    "let (??) = failwith \"should never hit this; this is just so the type checker doesn't croak on (??)\""
  in
  Compmisc.init_path false; (* This line makes Compmisc.initial_env magically work. *)
  Env.set_unit_name @@ Compenv.module_of_filename formatter fake_filename fake_filename;
  let (_, _, env_with_hole) =
    Typemod.type_structure
      (Compmisc.initial_env ()) (* Stdlib *)
      (Location.init buf fake_filename; Parse.implementation buf)
      (Location.in_file fake_filename)
  in
  env_with_hole

let string_of_error tenv err =
  ignore (Format.flush_str_formatter ());
  Typecore.report_error tenv Format.str_formatter err;
  Format.flush_str_formatter ()

let typedtree_sig_env_of_parsed parsed file_name =
  Env.set_unit_name @@ Compenv.module_of_filename formatter file_name file_name;
  (* print_endline @@ Compenv.module_of_filename formatter path path; *)
  let old_warning_printer = !Location.warning_printer in
  Location.warning_printer := (fun _ _ _ -> ());
  try
    let out = Typemod.type_structure initial_env parsed (Location.in_file file_name) in
    Location.warning_printer := old_warning_printer;
    out
  with e ->
    Location.warning_printer := old_warning_printer;
    raise e

let rec typedtree_sig_env_of_parsed_with_error_recovery parsed file_name =
  try
    let (tt, sig_, tenv) = typedtree_sig_env_of_parsed parsed file_name in
    (tt, sig_, tenv, [])
  with Typecore.Error (loc, err_env, err) as e ->
    (* Try to recover by replacing the troublesome location with a hole. *)
    let error_loc_replaced_with_hole =
      parsed
      |> Exp.replace loc { Exp.hole with pexp_loc = loc }
      |> Pat.replace loc { (Pat.any ()) with ppat_loc = loc }
    in
    if error_loc_replaced_with_hole <> parsed then
      let (tt, sig_, tenv, other_errors) = typedtree_sig_env_of_parsed_with_error_recovery error_loc_replaced_with_hole file_name in
      (tt, sig_, tenv, (loc, err_env, err) :: other_errors)
    else
      raise e

(* Returns (typedtree_structure, signature, env) *)
let typedtree_sig_env_of_file_with_error_recovery path =
  let parsed = Camlboot_interpreter.Interp.parse path in
  let (typed_struct, signature, env, errors) =
    typedtree_sig_env_of_parsed_with_error_recovery parsed path
  in
  (* Printtyped.implementation formatter typedtree;
  Printtyp.signature formatter signature;
  Format.pp_print_newline formatter (); *)
  (typed_struct, signature, env, errors)

let target_loc = ref Location.none
exception Found_exp of Typedtree.expression
module ExpFinder = TypedtreeIter.MakeIterator(struct
  include TypedtreeIter.DefaultIteratorArgument
  let enter_expression exp =
    if exp.Typedtree.exp_loc = !target_loc then raise (Found_exp exp)
end)
let find_exp_by_loc loc typed_struct =
  target_loc := loc;
  try ExpFinder.iter_structure typed_struct; None
  with Found_exp exp -> Some exp

(* Creates a function that given a loc might return a Typedtree.expression node *)
let type_lookups_of_typed_structure typed_struct : lookups =
  let exp_locmap = ref Loc_map.empty in
  let pat_locmap = ref Loc_map.empty in
  let module Iter = TypedtreeIter.MakeIterator(struct
    include TypedtreeIter.DefaultIteratorArgument
    let enter_expression exp =
      exp_locmap := Loc_map.add_to_loc exp.Typedtree.exp_loc exp !exp_locmap
    let enter_pattern pat =
      pat_locmap := Loc_map.add_to_loc pat.Typedtree.pat_loc pat !pat_locmap
  end) in
  Iter.iter_structure typed_struct;
  let exp_locmap = !exp_locmap in
  let pat_locmap = !pat_locmap in
  { lookup_exp =
      begin fun loc ->
        match Loc_map.all_at_loc loc exp_locmap with
        | []       -> None
        | [tt_exp] -> Some tt_exp
        | _        -> print_endline @@ "multiple exp typedtree nodes at loc " ^ Loc.to_string loc; None
      end
  ; lookup_pat =
      begin fun loc ->
        match Loc_map.all_at_loc loc pat_locmap with
        | []       -> None
        | [tt_pat] -> Some tt_pat
        | _        -> print_endline @@ "multiple pat typedtree nodes at loc " ^ Loc.to_string loc; None
      end
  }

(* let exp_typed_lookup_of_file path =
  let (typed_struct, _, _) = typedtree_sig_env_of_file path in
  exp_typed_lookup_of_typed_structure typed_struct *)

let exp_typed_lookup_of_parsed_with_error_recovery parsed file_name =
  let (typed_struct, _, _, _) = typedtree_sig_env_of_parsed_with_error_recovery parsed file_name in
  (type_lookups_of_typed_structure typed_struct).lookup_exp

(* let type_expression_opt ?(type_env = initial_env) exp =
  try Some (Typecore.type_expression type_env exp).exp_type
  with _ -> None *)

(* Types the expression and creates a map that given a loc returns the corresponding Typedtree.expression nodes *)
(* let loc_to_type_of_expression type_env exp =
  let typed_exp = Typecore.type_expression type_env exp in
  let locmap = ref Loc_map.empty in
  let module Iter = TypedtreeIter.MakeIterator(struct
    include TypedtreeIter.DefaultIteratorArgument
    let enter_expression exp =
      locmap := Loc_map.add_to_loc exp.Typedtree.exp_loc exp !locmap
  end) in
  Iter.iter_expression typed_exp;
  !locmap *)

let type_of_longident lid tenv =
  let (_, val_desc) = Env.lookup_value lid tenv in
  val_desc.val_type

let type_of_name name tenv =
  type_of_longident (Longident.Lident name) tenv

(* Returns number of args and func type unified with the desired return type. Need to explicitly remember number of args in case desired return type is an arrow. *)
let rec can_produce_typ t target_t =
  let t = Type.regular t in
  let try_right () =
    (* print_endline "try_right"; *)
    begin match t.desc with
    | Types.Tarrow (Asttypes.Nolabel, _, t_r, _) ->
      can_produce_typ t_r target_t
      |>&& begin fun (arg_count, t_r') ->
        Type.(unify_mutating_opt (copy t) (arrow (new_var ()) t_r'))
        |>& (fun t' -> (arg_count + 1, t'))
      end
    | _ -> None
    end
  in
  begin match Type.unify_opt t target_t with
  | Some t ->
    (* print_endline "unify1 success"; *)
    if not (Type.is_var_type target_t && Type.is_arrow_type t) (* no partial applications at type 'a *)
    then Some (0, t)
    else try_right ()
  | None -> try_right ()
  end

