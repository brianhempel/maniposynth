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
  | DropValueIntoExp of string * string (* loc str, vtrace str *) *)
  | AddVis           of string * string (* loc str, vis str *)
  | RemoveVis        of string * string (* loc str, vis str *)
  | ReplaceLoc       of string * string (* loc str, code str *)
  | DeleteLoc        of string (* loc str *)
  | NewAssert        of string * string * string (* loc str, lhs code str, rhs code str *)
  | Undo
  | Redo
  | DoSynth
  | InsertCode       of string * string (* vbs loc str, code *)
  | SetPos           of string * int * int (* loc str, x, y *)
  | MoveVb           of string * string * (int * int) option (* target vb loc str, mobile vb, new pos opt *)

(* Manual decoding because yojson_conv_lib messed up merlin and I like editor tooling. *)
let t_of_yojson (action_yojson : Yojson.Safe.t) =
  match action_yojson with
  (* | `List [`String "DropValueIntoVbs"; `String vbs_loc_str; `String vtrace_str]      -> DropValueIntoVbs (vbs_loc_str, vtrace_str)
  | `List [`String "DropValueIntoExp"; `String loc_str; `String vtrace_str]          -> DropValueIntoExp (loc_str, vtrace_str) *)
  | `List [`String "AddVis"; `String loc_str; `String vis_str]                       -> AddVis (loc_str, vis_str)
  | `List [`String "RemoveVis"; `String loc_str; `String vis_str]                    -> RemoveVis (loc_str, vis_str)
  | `List [`String "ReplaceLoc"; `String loc_str; `String code]                      -> ReplaceLoc (loc_str, code)
  | `List [`String "DeleteLoc"; `String loc_str]                                     -> DeleteLoc loc_str
  | `List [`String "NewAssert"; `String loc_str; `String lhs_code; `String rhs_code] -> NewAssert (loc_str, lhs_code, rhs_code)
  | `List [`String "DoSynth"]                                                        -> DoSynth
  | `List [`String "Undo"]                                                           -> Undo
  | `List [`String "Redo"]                                                           -> Redo
  | `List [`String "InsertCode"; `String vbs_loc_str; `String code]                  -> InsertCode (vbs_loc_str, code)
  | `List [`String "SetPos"; `String loc_str; `Int x; `Int y]                        -> SetPos (loc_str, x, y)
  | `List [`String "MoveVb"; `String vbs_loc_str; `String mobile_vb_loc_str
          ; `List [`String "None"]]                                                  -> MoveVb (vbs_loc_str, mobile_vb_loc_str, None)
  | `List [`String "MoveVb"; `String vbs_loc_str; `String mobile_vb_loc_str
          ; `List [`String "Some"; `Int x; `Int y]]                                  -> MoveVb (vbs_loc_str, mobile_vb_loc_str, Some (x,y))
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
      |> StructItems.concat_map_by_loc loc (fun si -> [Ast_helper.Str.value Asttypes.Nonrecursive [vb']; si])
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
  (* Preserve old attrs and loc. *)
  old
  |> Exp.map_by_loc loc begin fun exp -> { exp with pexp_desc = (Exp.from_string code).pexp_desc } end
  |> Pat.map_by_loc loc begin fun pat -> { pat with ppat_desc = (Pat.from_string code).ppat_desc } end
  |> Bindings.fixup final_tenv

let add_assert_before_loc loc lhs_code rhs_code final_tenv old =
  let assert_exp = Exp.assert_ @@ Exp.from_string @@ "(" ^ lhs_code ^ ") = (" ^ rhs_code ^ ")" in
  old
  (* |> Exp.map_by_loc loc (Exp.let_ Nonrecursive [Vb.mk (Pat.any ()) assert_exp]) *)
  |> Exp.map_by_loc loc (Exp.sequence assert_exp)
  |> Bindings.fixup final_tenv

let insert_code loc code final_tenv old =
  let exp = Exp.from_string code in
  let name = Name.gen_from_exp exp old in
  let vb' =  Vb.mk (Pat.var name) exp in
  if old = [] then [Ast_helper.Str.value Asttypes.Nonrecursive [vb']] else
  old
  |> Exp.map_by_loc loc (Ast_helper.Exp.let_ Asttypes.Nonrecursive [vb'])
  |> StructItems.concat_map_by_loc loc (fun si -> [Ast_helper.Str.value Asttypes.Nonrecursive [vb']; si])
  |> Bindings.fixup final_tenv

let set_pos loc x y old =
  old
  |> Vb.map_by_loc  loc (Pos.set_vb_pos  x y)
  |> Exp.map_by_loc loc (Pos.set_exp_pos x y)

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
      | Some (_rhs_exp, _fexp, _argexp, expected_exp) when Exp.is_hole expected_exp -> locs_to_remove := exp.pexp_loc :: !locs_to_remove
      | _ -> ()
      end
    | _ -> ()
  end;
  List.fold_right (fun loc -> delete_vblike loc %> Exp.replace loc Exp.hole)
    !locs_to_remove
    old

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
    delete_vblike loc
    %> Exp.replace loc Exp.hole
    %> clear_asserts_with_hole_rhs (* The above step may produce e.g. `assert (x = (??))` which is a sign to delete the whole assert. *)
    %> Bindings.fixup final_tenv
  | NewAssert (loc_str, lhs_code, rhs_code) ->
    let loc = Serialize.loc_of_string loc_str in
    add_assert_before_loc loc lhs_code rhs_code final_tenv
  | DoSynth ->
    (* Synth is async. Don't change program here. *)
    Synth.try_async path;
    (fun prog -> prog)
  | Undo ->
    if Unix.fork () = 0 then Unix.execve "./UndoRedo.app/Contents/MacOS/applet" [||] [|"EDITOR=Visual Studio Code"; "CMD=undo"|];
    (fun prog -> prog)
  | Redo ->
    if Unix.fork () = 0 then Unix.execve "./UndoRedo.app/Contents/MacOS/applet" [||] [|"EDITOR=Visual Studio Code"; "CMD=redo"|];
    (fun prog -> prog)
  | InsertCode (loc_str, code) ->
    let loc = Serialize.loc_of_string loc_str in
    insert_code loc code final_tenv
  | SetPos (loc_str, x, y) ->
    let loc = Serialize.loc_of_string loc_str in
    set_pos loc x y
  | MoveVb (vbs_loc_str, mobile_loc_str, xy_opt) ->
    let vbs_loc       = Serialize.loc_of_string vbs_loc_str in
    let mobile_vb_loc = Serialize.loc_of_string mobile_loc_str in
    move_vb vbs_loc mobile_vb_loc xy_opt final_tenv
