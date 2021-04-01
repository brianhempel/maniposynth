(*
  Actions generated from the browser and set to server.
  Need to keep format in sync in maniposynth.js
*)

open Parsetree
open Ast

type t =
  | DropValueBeforeVb of string * string (* vd id str, value str *)
  [@@deriving yojson]


(* Selected Axioms of Fig 1.3 in Li, Huiqing and Thompson, Simon (2005) Formalisation of Haskell Refactorings.
 * Itself adapted from Ariola, Zena M. and Blom, Stefan (1997) Lambda Calculi plus Letrec.
 *
 * Primes indicate possible renaming.
 *
 * v ::= x | λx.e
 * e ::= v | e1 e2 | letrec D in e
 * D ::= · | x=e , D  (Unordered recursive declarations)
 *
 * (λx.e) e1  ≡  letrec x = e1 in e
 *
 * (letrec D in e) e1      ≡  letrec D' in e' e1
 * e1 (letrec D in e)      ≡  letrec D' in e1 e'
 * λx.(letrec D1,D2 in e)  ≡  letrec D2 in λx.(letrec D1 in e)  if defined_vars(D1) disjoint from free_vars(D2), and x ∉ free_vars(D2)
 *
 * letrec x = letrec D in e1, D1 in e  ≡  letrec x = e1', D', D1 in e
 * letrec D1 in letrec D in e = letrec D1, D' in e'
 *
 *)

(* START HERE: make a DSL for expressing these rewrites? c.f. ppx_metaquot *)

(* plan: ditch the local rewrite strategy. it's too much when the strategy for handling variable renaming is the same whether its local or global
1. assign unique names
2. move binding
3. resolve
*)

(* Search AST for target location and mobile vb and trigger an appropriate movement:

  None. In proper location, we're done.
  None, failure to find either target or vb. No results.
  Move up
      let y = e1 in
      let x = e in
      e2
      ➜
      let x' = e in
      let y = e1 in
      e2'
  Unnest
      let y =
        let x = e in
        e1 in
      e2
      ➜
      let x' = e in
      let y = e1' in
      e2
  Move above let, top level
      let y = e1
      let x = e
      e2
      ➜
      let x' = e
      let y = e1
      e2'
  Move above other, top level
      thing
      let x = e
      ➜
      let x' = e
      thing
  Unnest to top level
      let y =
        let x = e in
        e1
      ➜
      let x' = e
      let y = e1'
  Move out of fun
      fun x -> let x = e in e1
      ➜
      let x' = e in fun x -> e1'
  Move out of function
      function ... | pi -> let x = e in ei | ...
      ➜
      let x' = e in function ... | pi -> ei' | ...
  Move out of application lhs
      (let x = e in e1) e2 ...
      ➜
      let x' = e in e1' e2 ...
  Move out of application rhs
      e1 ... (let x = e in ei) ...
      ➜
      let x' = e in e1 ... ei' ...
  Move out of match/try scrutinee
      match/try let x = e in e1 with ...
      ➜
      let x' = e in match/try e1' with ...
  Move out of match/try branch
      match/try e1 with ... | pi -> let x = e in ei | ...
      ➜
      let x' = e in match/try e1 with ... | pi -> ei' | ...
  Move out of tuple
      (..., let x = e in e1, ...)
      ➜
      let x' = e in (..., e1', ...)
  Move out of ctor
      C (let x = e in e1)
      ➜
      let x = e in C e1
  Move out of record
      {...; l = let x = e in e1; ...}
      ➜
      let x' = e in {...; l = e1'; ...}
  Move out of projection
      (let x = e in e1).l
      ➜
      let x' = e in e1'.l
  Move out of ITE guard
      if let x = e in e1 then e2 else e3
      ➜
      let x' = e in if e1' then e2 else e3
  Move out of ITE then
      if e1 then let x = e in e2 else e3
      ➜
      let x' = e in if e1 then e2' else e3
  Move out of ITE else
      if e1 then e2 else let x = e in e3
      ➜
      let x' = e in if e1 then e2 else e3'
*)

(*
(* Only returns first of VBs in a group *)
let children_for_binding_movement : ast_node -> ast_node list = function
  | Exp { pexp_desc; _ } -> begin
    let cases_exps = List.map (fun {pc_rhs; _} -> Exp pc_rhs) in
    let exp e = Exp e in
    match pexp_desc with
    | Pexp_ident _                    -> []
    | Pexp_constant _                 -> []
    | Pexp_let (_r, vbs, e)           -> [Vbs vbs; Exp e]
    | Pexp_fun (_lab, def, p, e)      -> [Exp e] (* Ignoring guard exps in pattern *)
    | Pexp_function cases             -> cases_exps cases
    | Pexp_apply (e, args)            -> Exp e :: (args |>@ fun (_arg_label, arg_e) -> Exp arg_e)
    | Pexp_match (e, cases)           -> Exp e :: cases_exps cases
    | Pexp_try (e, pel)               -> Exp e :: cases_exps cases
    | Pexp_tuple es                   -> es |>@ exp
    | Pexp_construct (_, e_opt)       -> list_of_opt e_opt |>@ exp
    | Pexp_variant (_lab, e_opt)      -> list_of_opt e_opt |>@ exp
    | Pexp_record (fields, e_opt)     -> list_of_opt e_opt @ (fields |>@ fun (_, e) -> e) |>@ exp
    | Pexp_field (e, _)               -> [Exp e]
    | Pexp_setfield _                 -> failwith "mutation not supported"
    | Pexp_array es                   -> ex |>@ exp
    | Pexp_ifthenelse (e1, e2, e_opt) -> [e1; e2] @ list_of_opt e_opt |>@ exp
    | Pexp_sequence (e1, e2)          -> [Exp e1; Exp e2]
    | Pexp_while _                    -> failwith "while not supported"
    | Pexp_for _                      -> failwith "for not supported"
    | Pexp_coerce _                   -> failwith "coerce not supported"
    | Pexp_constraint (e, _)          -> [Exp e]
    | Pexp_send _                     -> failwith "send not supported"
    | Pexp_new _                      -> failwith "new not supported"
    | Pexp_setinstvar _               -> failwith "setinstvar not supported"
    | Pexp_override _                 -> failwith "override not supported"
    | Pexp_letmodule _                -> failwith "letmodule not supported"
    | Pexp_letexception _             -> failwith "letexception not supported"
    | Pexp_assert e                   -> [Exp e]
    | Pexp_lazy _                     -> failwith "lazy not supported"
    | Pexp_poly _                     -> failwith "poly not supported"
    | Pexp_object _                   -> failwith "object not supported"
    | Pexp_newtype _                  -> failwith "newtype not supported"
    | Pexp_pack _                     -> failwith "pack not supported"
    | Pexp_open _                     -> failwith "open not supported"
    | Pexp_extension _                -> failwith "extension not supported"
    | Pexp_unreachable                -> []
  end

  | Sis []         -> []
  | Sis (si::rest) -> begin
    (fun si_children -> si_children @ [Sis rest]) @@
    match si.pstr_desc with
    | Pstr_eval (e, _)     -> [Exp e]
    | Pstr_value (_r, vbs) -> [Vbs vbs]
    | Pstr_primitive _     -> []
    | Pstr_type _          -> []
    | Pstr_typext _        -> []
    | Pstr_exception _     -> []
    | Pstr_module _        -> failwith "module not supported"
    | Pstr_recmodule _     -> failwith "recmodule not supported"
    | Pstr_modtype _       -> failwith "recmodule not supported"
    | Pstr_open _          -> []
    | Pstr_class _         -> failwith "class not supported"
    | Pstr_class_type _    -> failwith "class_type not supported"
    | Pstr_include _       -> failwith "include not supported"
    | Pstr_extension _     -> failwith "extension not supported"
    | Pstr_attribute _     -> []
  end

  | Vbs []         -> []
  | Vbs (vb::rest) -> [Exp vb.pvb_expr; Vbs rest] *)



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

let move_vb_before_vb before_vb_loc vb_loc old =
  (* let (restore_names, old) = assign_unique_names old in *)
  (* print_endline "here"; *)
  let did_insert = ref false in
  let mobile_vb, old' = remove_vb vb_loc old in
  let try_insert_into_vbs vbs =
    if !did_insert then None else
    let vbs' = vbs |>@@ (fun vb -> if Vb.loc vb = before_vb_loc && not !did_insert then (did_insert := true; [mobile_vb; vb]) else [vb]) in
    if !did_insert then Some vbs' else None in
  let old'' =
    old' |> Exp.map begin fun e ->
      match e.pexp_desc with
      | Pexp_let (_, vb1::_, _) when Vb.loc vb1 = before_vb_loc ->
        if !did_insert then e else
        (did_insert := true; Ast_helper.Exp.let_ Asttypes.Nonrecursive [mobile_vb] e)
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
          let si' = Ast_helper.Str.value Asttypes.Nonrecursive [mobile_vb] in
          (did_insert := true; [si'; si])
        | Pstr_value (rec_flag, vbs) ->
          begin match try_insert_into_vbs vbs with
          | Some vbs' -> [{ si with pstr_desc = Pstr_value (rec_flag, vbs') }]
          | None      -> [si]
          end
        | _ -> [si]
      end
    end in
  if !did_insert then [old''] else []

(*
  1. Search the value trace for locations where the value is bound to a name.
  2. See if any of those bindings can be moved up/down to the location indicated by the user.
*)
let move_value_before_vb vb_loc (_, (vtrace : Camlboot_interpreter.Data.vtrace)) old : Ast.program list =
  (* print_endline (List.length vtrace |> string_of_int); *)
  (* Location.print Format.std_formatter vb_loc; *)
  (* 1. Search the value trace for locations where the value is let-bound to a name. *)
  vtrace
  |>@@ fun ((_, loc), _) -> Vb.all old |>@? (fun vb ->
    (* Location.print Format.std_formatter (Pat.loc (Vb.pat vb)); *)
    (* let pat_locs = vb |> Vb.pat |> Pat.flatten |>@ Pat.loc in
    pat_locs |> List.iter (fun ploc ->
      (* Format.pp_print_newline Format.std_formatter ();
      Location.print Format.std_formatter loc;
      Location.print Format.std_formatter ploc;
      Location.print_loc Format.std_formatter loc;
      Location.print_loc Format.std_formatter ploc;
      Format.pp_print_bool Format.std_formatter (loc = ploc) *)
      print_endline (Ast.Loc.to_string loc);
      print_endline (Ast.Loc.to_string ploc);
      print_endline (string_of_bool (loc = ploc))
    ); *)
    vb |> (Vb.pat %> Pat.flatten %> List.exists (Pat.loc %> (=) loc))
  )
  (* 2. See if any of those bindings can be moved up/down to the location indicated by the user. *)
  (* |>@@ fun asdf -> print_endline " i don't beleiv eit"; [asdf] *)
  |>@@ fun vb -> move_vb_before_vb vb_loc (Vb.loc vb) old
  (* [] *)

let insert_value_before _vb_loc _value _old =
  []

let drop_value_before vb_loc (value : Camlboot_interpreter.Data.value) old =
  match move_value_before_vb vb_loc value old with
  | new_prog::_ -> new_prog
  | []          -> begin
    match insert_value_before vb_loc value old with
    | new_prog::_ -> new_prog
    | []          -> old
  end



(*
Strategy 1: Move an existing binding
  1. Search the value trace for locations where the value is bound to a name.
  2. See if any of those bindings can be moved up/down to the location indicated by the user.

Strategy 2: Insert a new binding
  1. For a Intro/Use in the value trace...
  2. Move the associated expression into a new binding at the location indicated by the user 3. Replace the expression with a reference to the variable
*)

let f : t -> Ast.program -> Ast.program = function
  | DropValueBeforeVb (vb_loc_str, value_str) ->
    let vb_loc = Serialize.loc_of_string vb_loc_str in
    let value = Serialize.value_of_string value_str in
    drop_value_before vb_loc value
