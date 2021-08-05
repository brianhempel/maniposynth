(* For making a lookup table of the expression types of a program. *)

open Shared
open Shared.Ast

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

let rec typedtree_sig_env_of_parsed parsed file_name =
  Env.set_unit_name @@ Compenv.module_of_filename formatter file_name file_name;
  (* print_endline @@ Compenv.module_of_filename formatter path path; *)
  let old_warning_printer = !Location.warning_printer in
  Location.warning_printer := (fun _ _ _ -> ());
  try
    let out = Typemod.type_structure initial_env parsed (Location.in_file file_name) in
    Location.warning_printer := old_warning_printer;
    out
  with Typecore.Error (loc, _env, _err) ->
    Location.warning_printer := old_warning_printer;
    (* Typecore.report_error env formatter err; *)
    typedtree_sig_env_of_parsed (Exp.replace loc Exp.hole parsed) file_name
    (* print_endline "";
    failwith "typedtree conversion failed" *)

(* Returns (typedtree_structure, signature, env) *)
let typedtree_sig_env_of_file path =
  let parsed = Camlboot_interpreter.Interp.parse path in
  let (typed_struct, signature, env) =
    typedtree_sig_env_of_parsed parsed path
  in
  (* Printtyped.implementation formatter typedtree;
  Printtyp.signature formatter signature;
  Format.pp_print_newline formatter (); *)
  (typed_struct, signature, env)

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

let exp_typed_lookup_of_parsed parsed file_name =
  let (typed_struct, _, _) = typedtree_sig_env_of_parsed parsed file_name in
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
