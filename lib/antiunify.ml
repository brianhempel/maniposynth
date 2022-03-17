open Shared.Ast
open Shared.Util

(*

Subsitution is the operation of applying the bindings in σ to type T to produce a type U...

σT = U

We want the reverse. Given a specific type U, what are all the possible substitutions and
generalizations σᵢTᵢ that could produce it?

U = σ₁T₁
U = σ₂T₂
U = σ₃T₃
...etc...

So that if a call on a function happens at specific types of U₁, U₂, etc., we can find the
intersection of the possible substitutions and types to acquire a most general form.

e.g. if see the following examples:
assert @@ unzip [(0, 0)]       = ([0], [0])
assert @@ unzip [(true, true)] = ([true], [true])

Those are calls at the concrete types:
unzip : (int * int) list   -> (int list, int list)
unzip : (bool * bool) list -> (bool list, bool list)

This first can be generalized...
['a : (int * int) list   -> (int list, int list)] 'a
['a : (int * int) list, 'b : (int list, int list)] 'a -> 'b
...

*)

type subst = (string * Types.type_expr) list

type t = subst * Types.type_expr

let to_string (subst, typ) =
  let subst_str =
    subst
    |>@ (fun (name, typ) -> "[" ^ name ^ " : " ^ Type.to_string typ ^ "]")
    |> String.concat ""
  in
  subst_str ^ " " ^ Type.to_string typ

let rename name name' ((subst, typ) : t) : t =
  let f typ =
    let open Types in
    match typ.desc with
    | Tvar    (Some str) when str = name -> { typ with desc = Tvar    (Some name') }
    | Tunivar (Some str) when str = name -> { typ with desc = Tunivar (Some name') }
    | _                                  -> typ
  in
  ( subst |>@ (fun (str, typ) -> ((if str = name then name' else str), Type.map f typ))
  , Type.map f typ
  )

let all_ways_to_possibly_reuse_binding name1 t1 ((subst2, typ2) : t) : t list =
  subst2
  |> List.fold_left begin fun outs (name2, t2) ->
    if Type.equal_ignoring_id_and_scope t1 t2 then (* Then we can either use name1 or name2 *)
      let using_name1 =
        outs
        |>@ begin fun (subst2, typ2) ->
          ( subst2 |>@? (fst %> (<>) name2)
          , typ2
          ) |> rename name2 name1
        end
      in
      let using_name2 = outs in
      using_name1 @ using_name2
    else
      outs
  end [(subst2, typ2)]

(* let names (subst, typ) =
  let subst_names =
    (subst |>@ fst)
    @ begin (subst |>@ snd) |>@@ Type.flatten |>@& Type.tvar_name end
  in
  let typ_names =
  in
  List.dedup @@ subst_names @ typ_names *)
(*
  Renames vars in subst2 & typ2 so no collsions.

  Also produces all combinations where a binding in s1 may be reused in s2.
*)
let combine_substs ((subst1, typ1) : t) ((subst2, typ2) : t) : t list =
  let domain1 = List.dedup @@ (subst1 |>@ fst) @ (typ1::(subst1 |>@ snd) |>@@ Type.names) in
  let domain2 = List.dedup @@ (subst2 |>@ fst) @ (typ2::(subst2 |>@ snd) |>@@ Type.names) in
  let names = domain1 @ domain2 in
  domain2
  |> List.fold_left begin fun outs name ->
    let outs_renamed =
      if List.mem name domain1 then
        let name' = Name.gen_ ~avoid:names ~base_name:"a" in
        outs |>@ rename name name'
      else
        outs
    in
    (* If there's a binding in subst1 that has the same type_expr as in subst2, we can consolidate. e.g. turn [a:int][b:int]('a,'b) into [a:int]('a,'a) *)
    let perhaps_consolidated =
      match List.assoc_opt name subst1 with
      | Some typ1 ->
        outs_renamed
        |>@@ all_ways_to_possibly_reuse_binding name typ1
      | None ->
        outs_renamed
    in
    perhaps_consolidated
  end [(subst2, typ2)]
  |>@ fun (subst2', typ2') -> (subst1 @ subst2', typ2')


let rec generalizations typ : t list =
  let recurse = generalizations in
  let open Types in
  (* let concat_map = List.concat_map in *)
  (* let rec flatten_row_field = function
  | Rpresent (Some t)                                 -> flatten t
  | Rpresent None                                     -> []
  | Reither (_, ts, _, { contents = Some row_field }) -> concat_map flatten ts @ flatten_row_field row_field
  | Reither (_, ts, _, { contents = None })           -> concat_map flatten ts
  | Rabsent                                           -> []
  in
  *)
  let new_var = Btype.newgenvar ~name:"a" () in
  ([ ("a", typ) ], new_var) ::
  match typ.desc with
  | Tvar _                                   -> [([], typ)]
  | Tarrow (lab, l, r, commutable)           ->
    recurse l |>@@ begin fun (lsubst, ltyp) ->
      recurse r |>@@ begin fun (rsubst, rtyp) ->
        combine_substs (lsubst, ltyp) (rsubst, rtyp) |>@@  begin fun (subst, rtyp) ->
          [ (subst, { typ with desc = Tarrow (lab, ltyp, rtyp, commutable) }) ]
        end
      end
    end
  | Tlink t                                  -> recurse t |>@ Tup2.map_snd (fun t' -> { typ with desc = Tlink t' })
  | Tsubst t                                 -> recurse t |>@ Tup2.map_snd (fun t' -> { typ with desc = Tsubst t' })
  | _                                        -> [([], typ)]
  (* | Ttuple ts                                -> []
  | Tconstr (_, ts, _)                       -> []
  | Tobject (t, { contents = Some (_, ts) }) -> []
  | Tobject (t, { contents = None })         -> []
  | Tfield (_, _, t1, t2)                    -> []
  | Tnil                                     -> []
  | Tunivar _                                -> []
  | Tpoly (t, ts)                            -> []
  | Tpackage (_, _, ts)                      -> []
  | Tvariant { row_fields; row_more; row_name = Some (_, ts); _ } -> []
  | Tvariant { row_fields; row_more; row_name = None;         _ } -> [] *)


(*
  Annoyingly, for type printing and almost certainly other purposes, TVars with the
  same name are not actually the same...they must be the physically same memory.

  Make it so.
*)
let fixup_tvars (subst, t) : t =
  let canonical_tvars : (string * Types.type_expr) list ref = ref [] in
  let fixup_typ typ =
    typ |> Type.map begin fun t ->
      match t.desc with
      | Tvar (Some name) ->
        begin match List.assoc_opt name !canonical_tvars with
        | Some canonical_tvar -> canonical_tvar
        | None ->
          canonical_tvars := (name, t) :: !canonical_tvars;
          t
        end
      | _ -> t
    end
  in
  ( subst |>@ Tup2.map_snd fixup_typ
  , fixup_typ t
  )

let generalizations typ : t list =
  generalizations typ
  |>@ fixup_tvars

(* START HERE: It's working! Now to actually use the lattice *)

let _ =
  Type.from_string ~env:Typing.initial_env "int -> int"
  |> generalizations
  |> List.iter (to_string %> print_endline)
