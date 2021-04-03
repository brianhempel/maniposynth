(*
  Actions generated from the browser and set to server.
  Need to keep format in sync in maniposynth.js
*)

open Parsetree
open Ast

type t =
  | DropValueBeforeVb of string * string (* vd id str, value str *)

(* Manual decoding because yojson_conv_lib messed up merlin and I like editor tooling. *)
let t_of_yojson (action_yojson : Yojson.Safe.t) =
  match action_yojson with
  | `List [`String "DropValueBeforeVb"; `String vb_id_str; `String value_str] -> DropValueBeforeVb (vb_id_str, value_str)
  | _                                                                         -> failwith "bad action json"

type value = Camlboot_interpreter.Data.value
type vtrace = Camlboot_interpreter.Data.vtrace


(* plan: ditch the local rewrite strategy. it's too much when the strategy for handling variable renaming is the same whether its local or global
1. assign unique names
2. move binding
3. resolve
*)

let remove_vb vb_loc old =
  let removed_vb = ref None in
  let remove vbs =
    if !removed_vb != None then vbs else
    match vbs |> partition (Vb.loc %> (=) vb_loc) with
    | ([vb], vbs') -> removed_vb := Some vb; vbs'
    | (_::_::_, _) -> failwith "remove_vb: multiple matching vbs...waaat?"
    | _            -> vbs in
  let old' =
    old |> Exp.map begin fun e ->
      match e.pexp_desc with
      | Pexp_let (rec_flag, vbs, body) ->
        (match remove vbs with [] -> body | vbs' -> { e with pexp_desc = Pexp_let (rec_flag, vbs', body) })
      | _ -> e
    end |> StructItem.map begin fun si ->
      match si.pstr_desc with
      | Pstr_value (rec_flag, vbs) -> { si with pstr_desc = Pstr_value (rec_flag, remove vbs) }
      | _ -> si
    end |> StructItems.map begin fun sis ->
      sis |>@? (fun si -> match si.pstr_desc with Pstr_value (_, []) -> false | _ -> true)
    end in
  match !removed_vb with
  | Some vb -> (vb, old')
  | None    -> failwith "remove_vb: Could not find vb"

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
  let mobile_vb, old' = remove_vb vb_loc old in
  insert_vb_before_vb before_vb_loc mobile_vb old'

(*
  1. Search the value trace for locations where the value is bound to a name.
  2. See if any of those bindings can be moved up/down to the location indicated by the user.
*)
let move_value_before_vb vb_loc (_, (vtrace : vtrace)) old : Ast.program list =
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
let insert_value_before vb_loc (_, (vtrace : vtrace)) old =
  let all_exps = Exp.all old in
  vtrace
  |>@@ (fun ((_, loc), _) -> all_exps |>@? (Exp.loc %> (=) loc))
  |>@@ begin fun e ->
    let name = "neeeeeew_var" in
    let vb' = Vb.mk (Pat.var name) e in
    old
    |> Exp.replace (Exp.loc e) (Exp.var name)
    |> insert_vb_before_vb vb_loc vb'
  end

(*
Strategy 1: Move an existing binding
  1. Search the value trace for locations where the value is bound to a name.
  2. See if any of those bindings can be moved up/down to the location indicated by the user.

Strategy 2: Insert a new binding
  1. For a Intro/Use in the value trace...
  2. Move the associated expression into a new binding at the location indicated by the user 3. Replace the expression with a reference to the variable
*)
let drop_value_before vb_loc (value : value) old =
  match move_value_before_vb vb_loc value old with
  | new_prog::_ -> new_prog
  | []          -> begin
    match insert_value_before vb_loc value old with
    | new_prog::_ -> new_prog
    | []          -> old
  end

let f : t -> Ast.program -> Ast.program = function
  | DropValueBeforeVb (vb_loc_str, value_str) ->
    let vb_loc = Serialize.loc_of_string vb_loc_str in
    let value = Serialize.value_of_string value_str in
    drop_value_before vb_loc value
