(*
  Actions generated from the browser and set to server.
  Need to keep format in sync in maniposynth.js
*)

open Parsetree
(* open Camlboot_interpreter.Data *)
open Shared.Ast
open Shared.Util

type t =
(*   | DropValueIntoVbs of string * string (* vbs loc str, vtrace str *)
  | DropValueIntoExp             of string * string (* loc str, vtrace str *) *)
  | AddVis                       of string * string (* loc str, vis str *)
  | RemoveVis                    of string * string (* loc str, vis str *)
  | ReplaceLoc                   of string * string (* loc str, code str *)
  | DeleteLoc                    of string (* loc str *)
  | NewAssert                    of string * string * string * (int * int) option (* loc str, lhs code str, rhs code str, pos opt *)
  | Undo
  | Redo
  | DoSynth
  | AcceptSynthResult            of string (* loc *)
  | RejectSynthResult            of string (* loc *)
  | RejectSynthResultAndContinue of string (* loc *)
  | InsertCode                   of string * string * (int * int) option (* vbs loc str, code, pos opt *)
  | Destruct                     of string * string  (* vbs loc str, scrutinee code *)
  | SetPos                       of string * int * int (* loc str, x, y *)
  | MoveVb                       of string * string * (int * int) option (* target vb loc str, mobile vb, new pos opt *)
  | SetRecFlag                   of string * bool (* vb loc str, is rec *)

(* Manual decoding because yojson_conv_lib messed up merlin and I like editor tooling. *)
let t_of_yojson (action_yojson : Yojson.Safe.t) =
  let float_or_int_to_int = function
    | `Float x -> int_of_float x
    | `Int x   -> x
    | _        -> failwith @@ "bad number in action json " ^ Yojson.Safe.to_string action_yojson
  in
  match action_yojson with
  (* | `List [`String "DropValueIntoVbs"; `String vbs_loc_str; `String vtrace_str]      -> DropValueIntoVbs (vbs_loc_str, vtrace_str)
  | `List [`String "DropValueIntoExp"; `String loc_str; `String vtrace_str]          -> DropValueIntoExp (loc_str, vtrace_str) *)
  | `List [`String "AddVis"; `String loc_str; `String vis_str]                       -> AddVis (loc_str, vis_str)
  | `List [`String "RemoveVis"; `String loc_str; `String vis_str]                    -> RemoveVis (loc_str, vis_str)
  | `List [`String "ReplaceLoc"; `String loc_str; `String code]                      -> ReplaceLoc (loc_str, code)
  | `List [`String "DeleteLoc"; `String loc_str]                                     -> DeleteLoc loc_str
  | `List [`String "NewAssert"; `String loc_str; `String lhs_code; `String rhs_code
  ; `List [`String "None"]]                                                          -> NewAssert (loc_str, lhs_code, rhs_code, None)
  | `List [`String "NewAssert"; `String loc_str; `String lhs_code; `String rhs_code
          ; `List [`String "Some"; x; y]]                                            -> NewAssert (loc_str, lhs_code, rhs_code, Some (float_or_int_to_int x, float_or_int_to_int y))
  | `List [`String "DoSynth"]                                                        -> DoSynth
  | `List [`String "AcceptSynthResult"; `String loc_str]                             -> AcceptSynthResult loc_str
  | `List [`String "RejectSynthResult"; `String loc_str]                             -> RejectSynthResult loc_str
  | `List [`String "RejectSynthResultAndContinue"; `String loc_str]                  -> RejectSynthResultAndContinue loc_str
  | `List [`String "Undo"]                                                           -> Undo
  | `List [`String "Redo"]                                                           -> Redo
  | `List [`String "InsertCode"; `String vbs_loc_str; `String code
          ; `List [`String "None"]]                                                  -> InsertCode (vbs_loc_str, code, None)
  | `List [`String "InsertCode"; `String vbs_loc_str; `String code
          ; `List [`String "Some"; x; y]]                                            -> InsertCode (vbs_loc_str, code, Some (float_or_int_to_int x, float_or_int_to_int y))
  | `List [`String "Destruct"; `String vbs_loc_str; `String destruct_code]           -> Destruct (vbs_loc_str, destruct_code)
  | `List [`String "SetPos"; `String loc_str; x; y]                                  -> SetPos (loc_str, float_or_int_to_int x, float_or_int_to_int y)
  | `List [`String "MoveVb"; `String vbs_loc_str; `String mobile_vb_loc_str
          ; `List [`String "None"]]                                                  -> MoveVb (vbs_loc_str, mobile_vb_loc_str, None)
  | `List [`String "MoveVb"; `String vbs_loc_str; `String mobile_vb_loc_str
          ; `List [`String "Some"; x; y]]                                            -> MoveVb (vbs_loc_str, mobile_vb_loc_str, Some (float_or_int_to_int x, float_or_int_to_int y))
  | `List [`String "SetRecFlag"; `String vb_loc_str; `Bool is_rec]                   -> SetRecFlag (vb_loc_str, is_rec)
  | _                                                                                -> failwith @@ "bad action json " ^ Yojson.Safe.to_string action_yojson

(* plan: ditch the local rewrite strategy. it's too much when the strategy for handling variable renaming is the same whether its local or global
1. assign unique names (not done yet)
2. move binding
3. resolve (not done yet)
*)

let remove_vblike_opt vb_loc old =
  let removed_vb = ref None in
  let remove vbs =
    if !removed_vb != None then vbs else
    match vbs |> List.partition (Vb.loc %> (=) vb_loc) with
    | ([vb], vbs') -> removed_vb := Some vb; vbs'
    | (_::_::_, _) -> failwith "remove_vblike: multiple matching vbs...waaat?"
    | _            -> vbs
  in
  let old' = old |> VbGroups.map (fun (recflag, vbs) -> (recflag, remove vbs)) in
  match !removed_vb with
  | Some vb -> Some (vb, old')
  | None    ->
    let remove imperative_exp =
      if !removed_vb != None then Some imperative_exp else
      if imperative_exp.pexp_loc = vb_loc then begin
        (* Copy pos attr to vb *)
        removed_vb := Some (Vb.mk ~attrs:(Pos.exp_pos_attrs imperative_exp) Pat.unit (Pos.remove_exp_pos imperative_exp));
        None
      end else
        Some imperative_exp
    in
    let old' = old |> VbGroups.SequenceLike.map remove in
    begin match !removed_vb with
    | Some vb -> Some (vb, old')
    | None    -> None
    end

(* Fail if not found *)
let remove_vblike vb_loc old =
  match remove_vblike_opt vb_loc old with
  | Some (vb, old') -> (vb, old')
  | None            -> failwith "remove_vblike: Could not find vb"

(* Silent if not found *)
let delete_vblike vb_loc old =
  remove_vblike_opt vb_loc old |>& snd ||& old

(* let drop_value_into_vbs loc (vtrace : vtrace) old =
  let usable_pats = Bindings.pats_in_scope_at loc old |>@? Pat.is_name in
  vtrace
  |> List.findmap_opt begin fun ((_, val_loc), _) ->
    (* print_endline (Loc.to_string val_loc); *)
    usable_pats
    |> List.find_opt (Pat.loc %> (=) val_loc)
    |>&& Pat.name |>& begin fun name ->
      let vb' = Vb.mk (Pat.var (Name.gen old)) (Exp.var name) in
      old
      |> Exp.map_by_loc loc (Ast_helper.Exp.let_ Asttypes.Nonrecursive [vb'])
      |> StructItem.concat_map_by_loc loc (fun si -> [Ast_helper.Str.value Asttypes.Nonrecursive [vb']; si])
      |> Bindings.fixup
    end
  end
  ||& old *)

(* let drop_value_into_exp loc (vtrace : vtrace) old =
  let usable_pats = Bindings.pats_in_scope_at loc old |>@? Pat.is_name in
  vtrace
  |> List.findmap_opt begin fun ((_, val_loc), _) ->
    (* print_endline (Loc.to_string val_loc); *)
    usable_pats
    |> List.find_opt (Pat.loc %> (=) val_loc)
    |>&& Pat.name |>& begin fun name ->
      old
      |> Exp.replace loc (Exp.var name)
      |> Bindings.fixup
    end
  end
  ||& old *)

let add_vis_to_loc loc vis_str final_tenv old =
  old
  |> Exp.map_by_loc loc begin fun exp ->
    { exp with pexp_attributes = Vis.add_vis_str_to_attrs vis_str exp.pexp_attributes }
  end
  |> Pat.map_by_loc loc begin fun pat ->
    { pat with ppat_attributes = Vis.add_vis_str_to_attrs vis_str pat.ppat_attributes }
  end
  |> Bindings.fixup final_tenv

let remove_vis_from_loc loc vis_str old =
  old
  |> Exp.map_by_loc loc begin fun exp ->
    { exp with pexp_attributes = Vis.remove_vis_str_from_attrs vis_str exp.pexp_attributes }
  end
  |> Pat.map_by_loc loc begin fun pat ->
    { pat with ppat_attributes = Vis.remove_vis_str_from_attrs vis_str pat.ppat_attributes }
  end

let replace_loc_code loc code final_tenv old =
  (* If new code is a var pattern, try renaming *)
  let try_rename ?(loc = loc) ?(code = code) prog =
    match code |> Pat.from_string_opt |>&& Pat.single_name with
    | Some name' -> Scope.rename_pat_by_loc loc name' prog
    | None       -> prog
  in
  (* Preserve old attrs and loc. *)
  match Vb.find_opt loc old with (* Is loc a vb? *)
  | Some vb ->
    let vb' = Vb.from_string code in
    old
    |> try_rename ~loc:vb.pvb_pat.ppat_loc ~code:(Pat.to_string vb'.pvb_pat)
    |> Vb.map_by_loc loc begin fun vb -> { vb with pvb_pat = vb'.pvb_pat; pvb_expr = vb'.pvb_expr } end
    |> Bindings.fixup final_tenv
  | None ->
    old
    |> Exp.map_by_loc loc begin fun exp -> { exp with pexp_desc = (Exp.from_string code).pexp_desc } end
    |> try_rename
    |> Pat.map_by_loc loc begin fun pat -> { pat with ppat_desc = (Pat.from_string code).ppat_desc } end (* In case rename failed, just replace the pattern with whatever the user typed. *)
    |> StructItem.map_by_loc loc begin fun si -> { si with pstr_desc = (StructItem.from_string code).pstr_desc } end
    |> Bindings.fixup final_tenv

(* In the JS, all asserts are added at the top level (for now) *)
let add_assert_before_loc loc lhs_code rhs_code xy_opt final_tenv old =
  let set_vb_pos vb = match xy_opt with Some (x, y) -> Pos.set_vb_pos x y vb | None -> vb in
  let assert_exp = Exp.assert_ @@ Exp.from_string @@ "(" ^ lhs_code ^ ") = (" ^ rhs_code ^ ")" in
  let new_sis = [StructItem.value Nonrecursive [Vb.mk (Pat.unit) assert_exp |> set_vb_pos]] in
  Name.name_unnameds ~type_env:final_tenv @@
  Bindings.fixup final_tenv @@
  if old = [] then (* Empty program *)
    new_sis
  else
    old
    |> Exp.map_by_loc loc (Exp.sequence assert_exp)
    |> StructItem.concat_map_by_loc loc (fun si -> si :: new_sis) (* Top level loc is last item in top level. Insert at end of top level. *)

(* Loc could be at top level (need new struct item binding) or an exp (need new let) *)
(* OR code could be an entire struct item (e.g. "type nat = Z | S of nat") *)
let insert_code ?name loc code xy_opt final_tenv old =
  let set_pos vb = match xy_opt with Some (x, y) -> Pos.set_vb_pos x y vb | None -> vb in
  let exp_inserter, new_sis, new_exp_loc =
    try
      let exp = Exp.from_string code in (* This will fail if given a struct item *)
      let name = name ||&~ (fun _ -> Name.gen old) in
      let vb' =  Vb.mk (Pat.var name) exp |> Vb.freshen_locs |> set_pos (* Freshening required by name_unnameds *) in
      ( Ast_helper.Exp.let_ Asttypes.Nonrecursive [vb'] (* body unapplied here *)
      , [Ast_helper.Str.value Asttypes.Nonrecursive [vb']]
      , vb'.pvb_expr.pexp_loc
      )
    with Syntaxerr.Error _ ->
      (* If we could not parse as an exp, try parsing as a structure item *)
      let struct_items = StructItems.from_string code |>@ StructItem.freshen_locs (* Freshening required by name_unnameds *) in
      ( (fun exp -> exp)
      , struct_items |> Vb.map set_pos
      , Location.none
      )
  in
  let prog =
    Name.name_unnameds ~type_env:final_tenv @@
    Bindings.fixup final_tenv @@
    if old = [] then (* Empty program *)
      new_sis
    else
      old
      |> Exp.map_by_loc loc exp_inserter
      |> StructItem.concat_map_by_loc loc (fun si -> si :: new_sis) (* Top level loc is last item in top level. Insert at end of top level. *)
  in
  (* Turn inserted bare functions into calls. *)
  match Typing.exp_typed_lookup_of_parsed_with_error_recovery prog "unknown.ml" new_exp_loc with
  | Some { exp_type; _ } when Type.arrow_arg_count exp_type >= 1 ->
    prog
    |> Exp.map_by_loc new_exp_loc begin fun fexp ->
      Exp.apply_with_hole_args fexp (Type.arrow_arg_count exp_type)
    end
  | _ ->
    prog

(*
We have all sorts of beautiful transforms to put matches in the right place, provided the
match starts in the form:

let var = match ... with ... in

So, just insert such a binding, let the transforms do their work, then remove the binding.
*)
let destruct loc destruct_code final_tenv old =
  (* If a top level destruct, the JS will call insertCode instead to avoid removing the binding. *)
  insert_code ~name:"remove_me" loc destruct_code None final_tenv old
  |> VbGroups.map begin fun (recflag, vbs) ->
    (recflag, if (vbs |>@@ Vb.names) = ["remove_me"] then [] else vbs)
  end

let set_pos loc x y old =
  old
  |> Vb.map_by_loc  loc (Pos.set_vb_pos  x y)
  |> Exp.map_by_loc loc (Pos.set_exp_pos x y)
  |> Pat.map_by_loc loc (Pos.set_pat_pos x y)

let move_vb vbs_loc mobile_vb_loc xy_opt final_tenv old =
  let old = match xy_opt with Some (x,y) -> set_pos mobile_vb_loc x y old | None -> old in
  print_endline (StructItems.to_string old);
  let (vb, old') = remove_vblike mobile_vb_loc old in
  old'
  |> Exp.map_by_loc vbs_loc (Exp.let_ Asttypes.Nonrecursive [vb])
  |>@@ begin fun si ->
    if si.pstr_loc = vbs_loc
    then [Ast_helper.Str.value Asttypes.Nonrecursive [vb]; si]
    else [si]
  end
  |> VbGroups.unit_vbs_to_sequence
  |> Bindings.fixup final_tenv

let clear_asserts_with_hole_rhs old =
  let locs_to_remove = ref [] in
  old
  |> Exp.iter begin fun exp ->
    match exp.pexp_desc with
    | Pexp_assert e ->
      begin match Camlboot_interpreter.Eval.parse_assert e with
      | Some (_rhs_exp, expected_exp) when Exp.is_hole expected_exp -> locs_to_remove := exp.pexp_loc :: !locs_to_remove
      | _ -> ()
      end
    | _ -> ()
  end;
  List.fold_right (fun loc -> delete_vblike loc %> Exp.replace loc Exp.hole)
    !locs_to_remove
    old

let should_synth_afterward = function
  | DoSynth
  | RejectSynthResultAndContinue _ -> true
  | _ -> false

let f path final_tenv : t -> Shared.Ast.program -> Shared.Ast.program = function
  (* | DropValueIntoVbs (loc_str, vtrace_str) ->
    let loc = Serialize.loc_of_string loc_str in
    let vtrace = Serialize.vtrace_of_string vtrace_str in
    drop_value_into_vbs loc vtrace
  | DropValueIntoExp (loc_str, vtrace_str) ->
    let loc = Serialize.loc_of_string loc_str in
    let vtrace = Serialize.vtrace_of_string vtrace_str in
    drop_value_into_exp loc vtrace *)
  | AddVis (loc_str, vis_str) ->
    let loc = Serialize.loc_of_string loc_str in
    add_vis_to_loc loc vis_str final_tenv
  | RemoveVis (loc_str, vis_str) ->
    let loc = Serialize.loc_of_string loc_str in
    remove_vis_from_loc loc vis_str
  | ReplaceLoc (loc_str, code) ->
    let loc = Serialize.loc_of_string loc_str in
    replace_loc_code loc code final_tenv
  | DeleteLoc loc_str ->
    let loc = Serialize.loc_of_string loc_str in
    let delete exp =
      (* Replace match with first non-empty branch *)
      match exp.pexp_desc with
      | Pexp_match (_, cases) -> cases |>@ Case.rhs |> List.find_opt (Exp.is_hole %> not) ||& Exp.hole
      | _                     -> Exp.hole
    in
    delete_vblike loc
    %> Exp.map_by_loc loc delete
    %> clear_asserts_with_hole_rhs (* The above step may produce e.g. `assert (x = (??))` which is a sign to delete the whole assert. *)
    %> Bindings.fixup final_tenv
  | NewAssert (loc_str, lhs_code, rhs_code, xy_opt) ->
    let loc = Serialize.loc_of_string loc_str in
    add_assert_before_loc loc lhs_code rhs_code xy_opt final_tenv
  | DoSynth ->
    (* Synth handled by caller. *)
    (fun prog -> prog)
  | AcceptSynthResult loc_str ->
    let loc = Serialize.loc_of_string loc_str in
    let change_attrs e =
      e.pexp_attributes
      |> Attr.remove_name "not"
      |> Attr.remove_name "accept_or_reject"
    in
    Exp.map_by_loc loc (fun e -> { e with pexp_attributes = change_attrs e })
  | RejectSynthResult loc_str
  | RejectSynthResultAndContinue loc_str ->
    (* Synth handled by caller. *)
    let loc = Serialize.loc_of_string loc_str in
    let change_attrs e =
      e.pexp_attributes
      |> Attr.remove_name "accept_or_reject"
      |> Attr.add_exp "not" (Attrs.remove_all_deep_exp e)
    in
    Exp.map_by_loc loc (fun e -> { Exp.hole with pexp_attributes = change_attrs e })
  | Undo ->
    Undo_redo.undo path
  | Redo ->
    Undo_redo.redo path
  | InsertCode (loc_str, code, xy_opt) ->
    begin fun prog ->
      let loc = Serialize.loc_of_string loc_str in
      let insert_at_top_level = prog = [] || prog |> List.exists (StructItem.loc %> (=) loc) in
      let equality_lhs_rhs =
        match Camlboot_interpreter.Eval.parse_assert (Exp.from_string code) with
        | Some (lhs, rhs)             -> Some (Exp.to_string lhs, Exp.to_string rhs)
        | _                           -> None
        | exception Syntaxerr.Error _ -> None
      in
      begin match equality_lhs_rhs with
      | Some (lhs, rhs) when insert_at_top_level -> add_assert_before_loc loc lhs rhs xy_opt final_tenv prog
      | _                                        -> insert_code loc code xy_opt final_tenv prog
      end
    end
  | Destruct (loc_str, destruct_code) ->
    let loc = Serialize.loc_of_string loc_str in
    destruct loc destruct_code final_tenv
  | SetPos (loc_str, x, y) ->
    let loc = Serialize.loc_of_string loc_str in
    set_pos loc x y
  | MoveVb (vbs_loc_str, mobile_loc_str, xy_opt) ->
    let vbs_loc       = Serialize.loc_of_string vbs_loc_str in
    let mobile_vb_loc = Serialize.loc_of_string mobile_loc_str in
    move_vb vbs_loc mobile_vb_loc xy_opt final_tenv
  | SetRecFlag (vb_loc_str, is_rec) ->
    let vb_loc   = Serialize.loc_of_string vb_loc_str in
    let recflag' = if is_rec then Asttypes.Recursive else Asttypes.Nonrecursive in
    VbGroups.map begin fun (recflag, vbs) ->
      if vbs |> List.exists (Vb.loc %> (=) vb_loc)
      then (recflag', vbs)
      else (recflag, vbs)
    end
    %> Bindings.fixup final_tenv
