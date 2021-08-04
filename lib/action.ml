(*
  Actions generated from the browser and set to server.
  Need to keep format in sync in maniposynth.js
*)

open Parsetree
open Camlboot_interpreter.Data
open Shared.Ast
open Shared.Util

type t =
  | MoveValue  of string * string (* vb id str, vtrace str *)
  | AddVis     of string * string (* loc str, vis str *)
  | RemoveVis  of string * string (* loc str, vis str *)
  | EditLoc    of string * string (* loc str, code str *)
  | NewAssert  of string * string * string (* loc str, lhs code str, rhs code str *)
  | Undo
  | Redo
  | DoSynth
  | InsertCode of string (* code *)
  | SetPos     of string * int * int (* loc str, x, y *)
  | MoveVb     of string * string * (int * int) option (* target vb loc str, mobile vb, new pos opt *)
  | DeleteVb   of string (* vb loc str *)

(* Manual decoding because yojson_conv_lib messed up merlin and I like editor tooling. *)
let t_of_yojson (action_yojson : Yojson.Safe.t) =
  match action_yojson with
  | `List [`String "MoveValue"; `String vb_id_str; `String vtrace_str]               -> MoveValue (vb_id_str, vtrace_str)
  | `List [`String "AddVis"; `String loc_str; `String vis_str]                       -> AddVis (loc_str, vis_str)
  | `List [`String "RemoveVis"; `String loc_str; `String vis_str]                    -> RemoveVis (loc_str, vis_str)
  | `List [`String "EditLoc"; `String loc_str; `String code]                         -> EditLoc (loc_str, code)
  | `List [`String "NewAssert"; `String loc_str; `String lhs_code; `String rhs_code] -> NewAssert (loc_str, lhs_code, rhs_code)
  | `List [`String "DoSynth"]                                                        -> DoSynth
  | `List [`String "Undo"]                                                           -> Undo
  | `List [`String "Redo"]                                                           -> Redo
  | `List [`String "InsertCode"; `String code]                                       -> InsertCode code
  | `List [`String "SetPos"; `String loc_str; `Int x; `Int y]                        -> SetPos (loc_str, x, y)
  | `List [`String "MoveVb"; `String vbs_loc_str; `String mobile_vb_loc_str
          ; `List [`String "None"]]                                                  -> MoveVb (vbs_loc_str, mobile_vb_loc_str, None)
  | `List [`String "MoveVb"; `String vbs_loc_str; `String mobile_vb_loc_str
          ; `List [`String "Some"; `Int x; `Int y]]                                  -> MoveVb (vbs_loc_str, mobile_vb_loc_str, Some (x,y))
  | `List [`String "DeleteVb"; `String vb_loc_str]                                   -> DeleteVb vb_loc_str
  | _                                                                                -> failwith @@ "bad action json " ^ Yojson.Safe.to_string action_yojson

(* plan: ditch the local rewrite strategy. it's too much when the strategy for handling variable renaming is the same whether its local or global
1. assign unique names (not done yet)
2. move binding
3. resolve (not done yet)
*)

let remove_vblike vb_loc old =
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
  | Some vb -> (vb, old')
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
    | Some vb -> (vb, old')
    | None    -> failwith "remove_vblike: Could not find vb"
    end

(* If before_vb_loc is the first vb in a list, inserts a new let before. *)
(* Otherwise, inserts into the bindings list. *)
let insert_vb_before_vb before_vb_loc vb' old =
  let did_insert = ref false in
  let try_insert_into_vbs vbs =
    if !did_insert then None else
    let vbs' = vbs |>@@ (fun vb -> if Vb.loc vb = before_vb_loc && not !did_insert then (did_insert := true; [vb'; vb]) else [vb]) in
    if !did_insert then Some vbs' else None in
  let old' =
    old |> Exp.map begin fun e ->
      match e.pexp_desc with
      | Pexp_let (_, vb1::_, _) when Vb.loc vb1 = before_vb_loc ->
        if !did_insert then e else
        (did_insert := true; Ast_helper.Exp.let_ Asttypes.Nonrecursive [vb'] e)
      | Pexp_let (rec_flag, vbs, body) ->
        begin match try_insert_into_vbs vbs with
        | Some vbs' -> { e with pexp_desc = Pexp_let (rec_flag, vbs', body) }
        | None      -> e
        end
      | _ -> e
    end |> StructItems.map begin fun sis ->
      sis |>@@ begin fun si ->
        match si.pstr_desc with
        | Pstr_value (_, vb1::_) when Vb.loc vb1 = before_vb_loc ->
          if !did_insert then [si] else
          let si' = Ast_helper.Str.value Asttypes.Nonrecursive [vb'] in
          (did_insert := true; [si'; si])
        | Pstr_value (rec_flag, vbs) ->
          begin match try_insert_into_vbs vbs with
          | Some vbs' -> [{ si with pstr_desc = Pstr_value (rec_flag, vbs') }]
          | None      -> [si]
          end
        | _ -> [si]
      end
    end in
  if !did_insert then [old'] else []

let move_vb_before_vb before_vb_loc vb_loc old =
  (* let (restore_names, old) = assign_unique_names old in *)
  let mobile_vb, old' = remove_vblike vb_loc old in
  print_endline @@ StructItems.to_string old';
  insert_vb_before_vb before_vb_loc mobile_vb old'

(*
  1. Search the value trace for locations where the value is bound to a name.
  2. See if any of those bindings can be moved up/down to the location indicated by the user.
*)
let move_value_before_vb vb_loc (vtrace : vtrace) old : Shared.Ast.program list =
  (* 1. Search the value trace for locations where the value is let-bound to a name. *)
  let all_vbs = Vb.all old in
  vtrace
  |>@@ fun ((_, loc), _) -> all_vbs |>@? (fun vb ->
    vb |> (Vb.pat %> Pat.flatten %> List.exists (Pat.loc %> (=) loc))
  )
  (* 2. See if any of those bindings can be moved up/down to the location indicated by the user. *)
  |>@@ fun vb -> move_vb_before_vb vb_loc (Vb.loc vb) old

(*
  1. Search the value trace for locations where the value flows through an expression.
  2. Replace that expression with a variable and plop a new binding before the indicated vb.
*)
let insert_value_before vb_loc (vtrace : vtrace) old =
  let all_exps = Exp.all old in
  vtrace
  |>@@ (fun ((_, loc), _) -> all_exps |>@? (Exp.loc %> (=) loc))
  |>@@ begin fun e ->
    let name = Name.gen old in
    let vb' = Vb.mk (Pat.var name) e in
    old
    |> Exp.(replace (loc e) (var name))
    |> insert_vb_before_vb vb_loc vb'
  end

(*
Strategy 1: Move an existing binding
  1. Search the value trace for locations where the value is bound to a name.
  2. See if any of those bindings can be moved up/down to the location indicated by the user.

Strategy 2: Insert a new binding
  1. For a Intro/Use in the value trace...
  2. Move the associated expression into a new binding at the location indicated by the user
  3. Replace the expression with a reference to the variable
*)
let drop_value_before vb_loc (vtrace : vtrace) old =
  (* let print_locs locs prog =
    locs |> List.iter (Loc.name_of_origin prog %> print_endline) in
  let print_uses uses prog =
    uses |> List.iter begin fun (def_loc, use_loc) ->
      print_endline @@ Loc.name_of_origin prog def_loc ^ " <- " ^ Loc.string_of_origin prog use_loc
    end in
  let old_uses, old_free = Binding_preservation.binding_map_and_free [([], "asdf.ml", old)] in
  print_endline "Uses before:";
  print_uses old_uses old;
  print_endline "Free before:";
  print_locs old_free old; *)
  let new_prog =
    match move_value_before_vb vb_loc vtrace old with
    | new_prog::_ -> new_prog
    | []          ->
    begin match insert_value_before vb_loc vtrace old with
      | new_prog::_ -> new_prog
      | []          -> old
    end in
  (* let new_uses, new_free = Binding_preservation.binding_map_and_free [([], "asdf.ml", new_prog)] in
  print_endline "Uses after:";
  print_uses new_uses new_prog;
  print_endline "Free after:";
  print_locs new_free new_prog; *)
  new_prog
  |> Bindings.fixup

let add_vis_to_loc loc vis_str old =
  old
  |> Exp.map_by_loc loc begin fun exp ->
    { exp with pexp_attributes = Vis.add_vis_str_to_attrs vis_str exp.pexp_attributes }
  end
  |> Bindings.fixup

let remove_vis_from_loc loc vis_str old =
  old
  |> Exp.map_by_loc loc begin fun exp ->
    { exp with pexp_attributes = Vis.remove_vis_str_from_attrs vis_str exp.pexp_attributes }
  end

let replace_loc_code loc code old =
  (* Preserve old attrs and loc. *)
  old
  |> Exp.map_by_loc loc begin fun exp -> { exp with pexp_desc = (Exp.from_string code).pexp_desc } end
  |> Pat.map_by_loc loc begin fun pat -> { pat with ppat_desc = (Pat.from_string code).ppat_desc } end
  |> Bindings.fixup

let add_assert_before_loc loc lhs_code rhs_code old =
  let assert_exp = Exp.assert_ @@ Exp.from_string @@ "(" ^ lhs_code ^ ") = (" ^ rhs_code ^ ")" in
  old
  (* |> Exp.map_by_loc loc (Exp.let_ Nonrecursive [Vb.mk (Pat.any ()) assert_exp]) *)
  |> Exp.map_by_loc loc (Exp.sequence assert_exp)
  |> Bindings.fixup

let insert_code code old =
  let exp = Exp.from_string code in
  let name = Name.gen_from_exp exp old in
  let vb' =  Vb.mk (Pat.var name) exp in
  old @ [Ast_helper.Str.value Asttypes.Nonrecursive [vb']]
  |> Bindings.fixup

let set_pos loc x y old =
  old
  |> Vb.map_by_loc  loc (Pos.set_vb_pos  x y)
  |> Exp.map_by_loc loc (Pos.set_exp_pos x y)

let move_vb vbs_loc mobile_vb_loc xy_opt old =
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
  |> Bindings.fixup

let f path : t -> Shared.Ast.program -> Shared.Ast.program = function
  | MoveValue (vb_loc_str, vtrace_str) ->
    let vb_loc = Serialize.loc_of_string vb_loc_str in
    let vtrace = Serialize.vtrace_of_string vtrace_str in
    drop_value_before vb_loc vtrace
  | AddVis (loc_str, vis_str) ->
    let loc = Serialize.loc_of_string loc_str in
    add_vis_to_loc loc vis_str
  | RemoveVis (loc_str, vis_str) ->
    let loc = Serialize.loc_of_string loc_str in
    remove_vis_from_loc loc vis_str
  | EditLoc (loc_str, code) ->
    let loc = Serialize.loc_of_string loc_str in
    replace_loc_code loc code
  | NewAssert (loc_str, lhs_code, rhs_code) ->
    let loc = Serialize.loc_of_string loc_str in
    add_assert_before_loc loc lhs_code rhs_code
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
  | InsertCode code ->
    insert_code code
  | SetPos (loc_str, x, y) ->
    let loc = Serialize.loc_of_string loc_str in
    set_pos loc x y
  | MoveVb (vbs_loc_str, mobile_loc_str, xy_opt) ->
    let vbs_loc       = Serialize.loc_of_string vbs_loc_str in
    let mobile_vb_loc = Serialize.loc_of_string mobile_loc_str in
    move_vb vbs_loc mobile_vb_loc xy_opt
  | DeleteVb vb_loc_str ->
    let vb_loc = Serialize.loc_of_string vb_loc_str in
    remove_vblike vb_loc %> snd %> Bindings.fixup



