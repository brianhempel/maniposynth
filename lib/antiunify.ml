open Shared.Ast
open Shared.Util

(*

These functions are not optimized, but are not in the synthesis critical path.

See the bottom of this file for some test code you can uncomment and play with for understanding.

Given a concrete type inferred from a user example, e.g. int -> int, there are many possible generalizations:
[a : int -> int] 'a
[a : int] 'a -> 'a
[a : int][b : int] 'a -> 'b
[a : int] 'a -> int
[a : int] int -> 'a
 int -> int

We want to synthesize under the most specific possible one that is consistant will all the user examples.
The synthesizer will replace the type variables with specific polymorphic variant types, e.g. [`A] [`B] etc,
as a way to force those types to only unify with themselves.

More details:

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
unzip : (int  * int)  list -> (int  list * int  list)
unzip : (bool * bool) list -> (bool list * bool list)

This first can be generalized in many ways...
'a
'a -> 'b
'a -> 'b * 'b
'a -> 'b * 'c
'a -> 'b * 'c list
'a -> 'b * int list
'a -> 'b list * 'c
'a -> 'b list * 'b list
'a -> 'b list * 'c list
'a -> 'b list * int list
'a -> int list * 'b
'a -> int list * 'b list
'a -> int list * int list
'a list -> 'b
'a list -> 'b * 'b
'a list -> 'b * 'c
'a list -> 'b * 'c list
'a list -> 'b * int list
'a list -> 'b list * 'c
'a list -> 'b list * 'b list
'a list -> 'b list * 'c list
'a list -> 'b list * int list
'a list -> int list * 'b
'a list -> int list * 'b list
'a list -> int list * int list
('a * 'a) list -> 'b
('a * 'a) list -> 'b * 'b
('a * 'a) list -> 'b * 'c
('a * 'a) list -> 'b * 'a list
('a * 'a) list -> 'b * 'c list
('a * 'a) list -> 'b * int list
('a * 'a) list -> 'a list * 'b
('a * 'a) list -> 'b list * 'c
('a * 'a) list -> 'a list * 'a list
('a * 'a) list -> 'b list * 'b list
('a * 'a) list -> 'a list * 'a list
('a * 'a) list -> 'b list * 'a list
('a * 'a) list -> 'a list * 'b list
('a * 'a) list -> 'b list * 'c list
('a * 'a) list -> 'a list * int list
('a * 'a) list -> 'b list * int list
('a * 'a) list -> int list * 'b
('a * 'a) list -> int list * 'a list
('a * 'a) list -> int list * 'b list
('a * 'a) list -> int list * int list
('a * 'b) list -> 'c
('a * 'b) list -> 'c * 'c
('a * 'b) list -> 'c * 'd
('a * 'b) list -> 'c * 'a list
('a * 'b) list -> 'c * 'b list
('a * 'b) list -> 'c * 'd list
('a * 'b) list -> 'c * int list
('a * 'b) list -> 'a list * 'c
('a * 'b) list -> 'b list * 'c
('a * 'b) list -> 'c list * 'd
('a * 'b) list -> 'a list * 'a list
('a * 'b) list -> 'b list * 'b list
('a * 'b) list -> 'c list * 'c list
('a * 'b) list -> 'a list * 'a list
('a * 'b) list -> 'b list * 'a list
('a * 'b) list -> 'c list * 'a list
('a * 'b) list -> 'a list * 'b list
('a * 'b) list -> 'a list * 'c list
('a * 'b) list -> 'b list * 'b list
('a * 'b) list -> 'c list * 'b list
('a * 'b) list -> 'b list * 'c list
('a * 'b) list -> 'c list * 'd list
('a * 'b) list -> 'a list * int list
('a * 'b) list -> 'b list * int list
('a * 'b) list -> 'c list * int list
('a * 'b) list -> int list * 'c
('a * 'b) list -> int list * 'a list
('a * 'b) list -> int list * 'b list
('a * 'b) list -> int list * 'c list
('a * 'b) list -> int list * int list
('a * int) list -> 'b
('a * int) list -> 'b * 'b
('a * int) list -> 'b * 'c
('a * int) list -> 'b * 'a list
('a * int) list -> 'b * 'c list
('a * int) list -> 'b * int list
('a * int) list -> 'a list * 'b
('a * int) list -> 'b list * 'c
('a * int) list -> 'a list * 'a list
('a * int) list -> 'b list * 'b list
('a * int) list -> 'a list * 'a list
('a * int) list -> 'b list * 'a list
('a * int) list -> 'a list * 'b list
('a * int) list -> 'b list * 'c list
('a * int) list -> 'a list * int list
('a * int) list -> 'b list * int list
('a * int) list -> int list * 'b
('a * int) list -> int list * 'a list
('a * int) list -> int list * 'b list
('a * int) list -> int list * int list
(int * 'a) list -> 'b
(int * 'a) list -> 'b * 'b
(int * 'a) list -> 'b * 'c
(int * 'a) list -> 'b * 'a list
(int * 'a) list -> 'b * 'c list
(int * 'a) list -> 'b * int list
(int * 'a) list -> 'a list * 'b
(int * 'a) list -> 'b list * 'c
(int * 'a) list -> 'a list * 'a list
(int * 'a) list -> 'b list * 'b list
(int * 'a) list -> 'a list * 'a list
(int * 'a) list -> 'b list * 'a list
(int * 'a) list -> 'a list * 'b list
(int * 'a) list -> 'b list * 'c list
(int * 'a) list -> 'a list * int list
(int * 'a) list -> 'b list * int list
(int * 'a) list -> int list * 'b
(int * 'a) list -> int list * 'a list
(int * 'a) list -> int list * 'b list
(int * 'a) list -> int list * int list
(int * int) list -> 'a
(int * int) list -> 'a * 'a
(int * int) list -> 'a * 'b
(int * int) list -> 'a * 'b list
(int * int) list -> 'a * int list
(int * int) list -> 'a list * 'b
(int * int) list -> 'a list * 'a list
(int * int) list -> 'a list * 'b list
(int * int) list -> 'a list * int list
(int * int) list -> int list * 'a
(int * int) list -> int list * 'a list
(int * int) list -> int list * int list

As can the second:
'a
'a -> 'b
'a -> 'b * 'b
'a -> 'b * 'c
'a -> 'b * 'c list
'a -> 'b * bool list
'a -> 'b list * 'c
'a -> 'b list * 'b list
'a -> 'b list * 'c list
'a -> 'b list * bool list
'a -> bool list * 'b
'a -> bool list * 'b list
'a -> bool list * bool list
'a list -> 'b
'a list -> 'b * 'b
'a list -> 'b * 'c
'a list -> 'b * 'c list
'a list -> 'b * bool list
'a list -> 'b list * 'c
'a list -> 'b list * 'b list
'a list -> 'b list * 'c list
'a list -> 'b list * bool list
'a list -> bool list * 'b
'a list -> bool list * 'b list
'a list -> bool list * bool list
('a * 'a) list -> 'b
('a * 'a) list -> 'b * 'b
('a * 'a) list -> 'b * 'c
('a * 'a) list -> 'b * 'a list
('a * 'a) list -> 'b * 'c list
('a * 'a) list -> 'b * bool list
('a * 'a) list -> 'a list * 'b
('a * 'a) list -> 'b list * 'c
('a * 'a) list -> 'a list * 'a list
('a * 'a) list -> 'b list * 'b list
('a * 'a) list -> 'a list * 'a list
('a * 'a) list -> 'b list * 'a list
('a * 'a) list -> 'a list * 'b list
('a * 'a) list -> 'b list * 'c list
('a * 'a) list -> 'a list * bool list
('a * 'a) list -> 'b list * bool list
('a * 'a) list -> bool list * 'b
('a * 'a) list -> bool list * 'a list
('a * 'a) list -> bool list * 'b list
('a * 'a) list -> bool list * bool list
('a * 'b) list -> 'c
('a * 'b) list -> 'c * 'c
('a * 'b) list -> 'c * 'd
('a * 'b) list -> 'c * 'a list
('a * 'b) list -> 'c * 'b list
('a * 'b) list -> 'c * 'd list
('a * 'b) list -> 'c * bool list
('a * 'b) list -> 'a list * 'c
('a * 'b) list -> 'b list * 'c
('a * 'b) list -> 'c list * 'd
('a * 'b) list -> 'a list * 'a list
('a * 'b) list -> 'b list * 'b list
('a * 'b) list -> 'c list * 'c list
('a * 'b) list -> 'a list * 'a list
('a * 'b) list -> 'b list * 'a list
('a * 'b) list -> 'c list * 'a list
('a * 'b) list -> 'a list * 'b list
('a * 'b) list -> 'a list * 'c list
('a * 'b) list -> 'b list * 'b list
('a * 'b) list -> 'c list * 'b list
('a * 'b) list -> 'b list * 'c list
('a * 'b) list -> 'c list * 'd list
('a * 'b) list -> 'a list * bool list
('a * 'b) list -> 'b list * bool list
('a * 'b) list -> 'c list * bool list
('a * 'b) list -> bool list * 'c
('a * 'b) list -> bool list * 'a list
('a * 'b) list -> bool list * 'b list
('a * 'b) list -> bool list * 'c list
('a * 'b) list -> bool list * bool list
('a * bool) list -> 'b
('a * bool) list -> 'b * 'b
('a * bool) list -> 'b * 'c
('a * bool) list -> 'b * 'a list
('a * bool) list -> 'b * 'c list
('a * bool) list -> 'b * bool list
('a * bool) list -> 'a list * 'b
('a * bool) list -> 'b list * 'c
('a * bool) list -> 'a list * 'a list
('a * bool) list -> 'b list * 'b list
('a * bool) list -> 'a list * 'a list
('a * bool) list -> 'b list * 'a list
('a * bool) list -> 'a list * 'b list
('a * bool) list -> 'b list * 'c list
('a * bool) list -> 'a list * bool list
('a * bool) list -> 'b list * bool list
('a * bool) list -> bool list * 'b
('a * bool) list -> bool list * 'a list
('a * bool) list -> bool list * 'b list
('a * bool) list -> bool list * bool list
(bool * 'a) list -> 'b
(bool * 'a) list -> 'b * 'b
(bool * 'a) list -> 'b * 'c
(bool * 'a) list -> 'b * 'a list
(bool * 'a) list -> 'b * 'c list
(bool * 'a) list -> 'b * bool list
(bool * 'a) list -> 'a list * 'b
(bool * 'a) list -> 'b list * 'c
(bool * 'a) list -> 'a list * 'a list
(bool * 'a) list -> 'b list * 'b list
(bool * 'a) list -> 'a list * 'a list
(bool * 'a) list -> 'b list * 'a list
(bool * 'a) list -> 'a list * 'b list
(bool * 'a) list -> 'b list * 'c list
(bool * 'a) list -> 'a list * bool list
(bool * 'a) list -> 'b list * bool list
(bool * 'a) list -> bool list * 'b
(bool * 'a) list -> bool list * 'a list
(bool * 'a) list -> bool list * 'b list
(bool * 'a) list -> bool list * bool list
(bool * bool) list -> 'a
(bool * bool) list -> 'a * 'a
(bool * bool) list -> 'a * 'b
(bool * bool) list -> 'a * 'b list
(bool * bool) list -> 'a * bool list
(bool * bool) list -> 'a list * 'b
(bool * bool) list -> 'a list * 'a list
(bool * bool) list -> 'a list * 'b list
(bool * bool) list -> 'a list * bool list
(bool * bool) list -> bool list * 'a
(bool * bool) list -> bool list * 'a list
(bool * bool) list -> bool list * bool list

Some of those generalizations are shared:
'a
'a -> 'b
'a -> 'b * 'b
'a -> 'b * 'c
'a -> 'b * 'c list
'a -> 'b list * 'c
'a -> 'b list * 'b list
'a -> 'b list * 'c list
'a list -> 'b
'a list -> 'b * 'b
'a list -> 'b * 'c
'a list -> 'b * 'c list
'a list -> 'b list * 'c
'a list -> 'b list * 'b list
'a list -> 'b list * 'c list
('a * 'a) list -> 'b
('a * 'a) list -> 'b * 'b
('a * 'a) list -> 'b * 'c
('a * 'a) list -> 'b * 'a list
('a * 'a) list -> 'b * 'c list
('a * 'a) list -> 'a list * 'b
('a * 'a) list -> 'b list * 'c
('a * 'a) list -> 'a list * 'a list
('a * 'a) list -> 'b list * 'b list
('a * 'a) list -> 'b list * 'a list
('a * 'a) list -> 'a list * 'b list
('a * 'a) list -> 'b list * 'c list
('a * 'b) list -> 'c
('a * 'b) list -> 'c * 'c
('a * 'b) list -> 'c * 'd
('a * 'b) list -> 'c * 'a list
('a * 'b) list -> 'c * 'b list
('a * 'b) list -> 'c * 'd list
('a * 'b) list -> 'a list * 'c
('a * 'b) list -> 'b list * 'c
('a * 'b) list -> 'c list * 'd
('a * 'b) list -> 'a list * 'a list
('a * 'b) list -> 'b list * 'b list
('a * 'b) list -> 'c list * 'c list
('a * 'b) list -> 'b list * 'a list
('a * 'b) list -> 'c list * 'a list
('a * 'b) list -> 'a list * 'b list
('a * 'b) list -> 'a list * 'c list
('a * 'b) list -> 'c list * 'b list
('a * 'b) list -> 'b list * 'c list
('a * 'b) list -> 'c list * 'd list

But only one (I believe) is the most specific shared generalization:
('a * 'a) list -> 'a list * 'a list

The code below finds the possible generalizations for the given types,
intersects them, and picks out the most specific (the type that doesn't
change when unified with any of the others.)

LIMITATIONS:

Type variables in the _input_ types are not handled yet. They have a different meaning than type vars
in the output.

e.g. the most specific generalization of 'a -> int and int -> 'a *should* be int -> int, not 'a -> 'b.
But we can't handle that yet.

*)

type subst = (string * Types.type_expr) list

type st = subst * Types.type_expr

let subst_to_string subst =
  subst
  |>@ (fun (name, typ) -> "[" ^ name ^ " : " ^ Type.to_string typ ^ "]")
  |> String.concat ""

let to_string (subst, typ) =
  subst_to_string subst ^ " " ^ Type.to_string typ

let rename_all mapping ((subst, typ) : st) : st =
  ( subst |>@ (fun (str, typ) -> (List.assoc_opt str mapping ||& str, Type.rename_all mapping typ))
  , Type.rename_all mapping typ
  )

let rename name name' st : st =
  rename_all [(name, name')] st


(* Normalize the names so we can easily compare for alpha-equivalence. *)
let normalized_names = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m"; "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"] (* what are you doing with more type variables than that?! *)
let temp_names = normalized_names |>@ fun name -> name ^ "10000"
let temp_names_mapping = List.map2_best_effort (fun name name' -> (name, name')) normalized_names temp_names
let normalize_names st : st =
  let (subst, typ) = rename_all temp_names_mapping st in (* Avoid collisions if there are names in the subst that aren't in typ. *)
  let orig_names = Type.names typ in
  let mapping = List.map2_best_effort (fun name name' -> (name, name')) orig_names normalized_names in
  rename_all mapping (subst, typ)

(*
  Annoyingly, for type printing and almost certainly other purposes, TVars with the
  same name are not actually the same...they must be the physically same memory.

  Make it so.
*)
let fixup_tvars (subst, t) : st =
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

let all_ways_to_possibly_reuse_binding name1 t1 ((subst2, typ2) : st) : st list =
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


(*
  Renames vars in subst2 & typ2 so no collsions.

  Also produces all combinations where a binding in s1 may be reused in s2.
*)
let combine_substs subst1 typs1 ((subst2, typ2) : st) : st list =
  let domain1 = List.dedup @@ (subst1 |>@ fst) @ (typs1 @ (subst1 |>@ snd) |>@@ Type.names) in
  let domain2 = List.dedup @@ (subst2 |>@ fst) @ (typ2 :: (subst2 |>@ snd) |>@@ Type.names) in
  let names = ref (domain1 @ domain2) in
  domain2
  |> List.fold_left begin fun outs name ->
    if List.mem name domain1 then
      let name' = Name.gen_ ~avoid:!names ~base_name:"a" in
      names := name' :: !names;
      outs |>@ rename name name'
    else
      outs
  end [(subst2, typ2)]
  |>@@ begin fun (subst2', typ2') ->
    (* if true then [(subst2', typ2')] else *)
    (* If there's a binding in subst1 that has the same type_expr as in subst2, we can consolidate. e.g. turn [a:int][b:int]('a,'b) into [a:int]('a,'a) *)
    subst1
    |> List.fold_left begin fun outs (name1, t1) ->
      outs
      |>@@ (fun (subst2', typ2') -> all_ways_to_possibly_reuse_binding name1 t1 (subst2', typ2'))
    end [(subst2', typ2')]
  end
  |>@ fun (subst2', typ2') -> (subst1 @ subst2', typ2')

let rec combos typs : (subst * Types.type_expr list) list =
  typs
  |>@ generalizations
  |> List.cart_prod
  |>@@ begin fun sts ->
    sts |> List.fold_left begin fun outs st ->
      outs
      |>@@ begin fun (subst_so_far, ts_so_far) ->
        combine_substs subst_so_far ts_so_far st
        |>@ begin fun (subst_so_far', t) ->
          (subst_so_far', ts_so_far @ [t])
        end
      end
    end [([], [])]
  end

(* Combos, but for exactly two types *)
and pair_combos typ1 typ2 : (subst * (Types.type_expr * Types.type_expr)) list =
  combos [typ1; typ2]
  |>@ begin function
  | (subst, [t1; t2]) -> (subst, (t1, t2))
  | _                 -> failwith "Antiunify.pair_comobs shouldn't happen"
  end

and generalizations typ : st list =
  let recurse = generalizations in
  let open Types in
  let generalize_self_and_return outs =
    let name = Name.gen_ ~avoid:(Type.names typ) ~base_name:"a" in
    let new_var = Btype.newgenvar ~name:"a" () in
    ([ (name, typ) ], new_var) :: outs
  in
  generalize_self_and_return @@
  match typ.desc with
  | Tnil
  | Tunivar _
  | Tvar _                                  -> [([], typ)]
  | Tarrow (lab, l, r, commutable)          -> pair_combos l r   |>@ (fun (subst, (l', r'))     -> (subst, { typ with desc = Tarrow (lab, l', r', commutable) }))
  | Tlink t                                 -> recurse t         |>@ (fun (subst, t')           -> (subst, { typ with desc = Tlink t' }))
  | Tsubst t                                -> recurse t         |>@ (fun (subst, t')           -> (subst, { typ with desc = Tsubst t' }))
  | Ttuple ts                               -> combos ts         |>@ (fun (subst, ts')          -> (subst, { typ with desc = Ttuple ts' }))
  | Tconstr (path, ts, { contents = Mnil }) -> combos ts         |>@ (fun (subst, ts')          -> (subst, { typ with desc = Tconstr (path, ts', { contents = Mnil }) }))
  | Tfield (str, field_kind, t1, t2)        -> pair_combos t1 t2 |>@ (fun (subst, (t1', t2'))   -> (subst, { typ with desc = Tfield (str, field_kind, t1', t2') }))
  | Tpoly (t, ts)                           -> combos (t::ts)    |>@ (function (subst, t'::ts') -> (subst, { typ with desc = Tpoly (t', ts') }) | _ -> failwith "Antiunify.generalizations Tpoly shouldn't happen")
  | Tpackage (path, lids, ts)               -> combos ts         |>@ (fun (subst, ts')          -> (subst, { typ with desc = Tpackage (path, lids, ts') }))
  | Tvariant _                              -> failwith "Antiunify.generalizations not smart enough to handle polymorphic variants"
  | Tobject _                               -> failwith "Antiunify.generalizations not smart enough to handle objects"
  | Tconstr _                               -> failwith "Antiunify.generalizations not smart enough to handle abbrev memos"

let generalizations typ : st list =
  generalizations typ
  |>@ normalize_names
  |>@ fixup_tvars

let shared_generalizations typ1 typ2 : Types.type_expr list =
  let gens1 = generalizations typ1 |>@ snd |> List.dedup_by Type.to_string in
  let gens2 = generalizations typ2 |>@ snd in
  gens1 |>@? begin fun t1 ->
    List.exists (Type.equal_ignoring_id_and_scope t1) gens2
  end

(* O(n^2) *)
let most_specific_generalization typs =
  typs |>@? begin fun typ ->
    typs |> List.for_all (fun t -> t == typ || not (Type.is_equal_or_more_general_than typ t))
  end
  |> function
  | [t] -> t
  | ts  -> failwith @@ "most_specific_generalization: " ^ string_of_int (List.length ts) ^ " \"most specific\" generalizations!\n" ^ String.concat "\n" (ts |>@ Type.to_string)

(* let most_specific_shared_generalization typ1 typ2 =
  shared_generalizations typ1 typ2
  |> most_specific_generalization *)

let rec most_specific_shared_generalization_of_types typs =
  let recurse = most_specific_shared_generalization_of_types in
  match typs with
  | []        -> failwith "most_specific_shared_generalization_of_types shouldn't be given an empty list..."
  | [typ]     -> typ
  | typ::typs ->
    shared_generalizations typ (recurse typs)
    |> most_specific_generalization

(* Input types must not have type vars (for now). Shadow to prevent misuse. *)

let check_input_types typs =
  typs |> List.iter begin fun typ ->
    if List.exists Type.is_var_type (Type.flatten typ) then
      failwith "Antiunify.generalizations not smart enough to handle type variables in the input types";
  end

let generalizations typ =
  check_input_types [typ];
  generalizations typ

let shared_generalizations typ1 typ2 =
  check_input_types [typ1; typ2];
  shared_generalizations typ1 typ2

let most_specific_shared_generalization_of_types typs =
  check_input_types typs;
  most_specific_shared_generalization_of_types typs

(* let _ =
  Type.from_string ~env:Typing.initial_env "int -> int"
  |> generalizations
  |> List.iter (to_string %> print_endline) *)

(* let _ =
  Type.from_string ~env:Typing.initial_env "int * int * int"
  |> generalizations
  |> List.iter (to_string %> print_endline) *)

(* let _ =
  Type.from_string ~env:Typing.initial_env "int * int * int"
  |> generalizations
  |>@ snd
  |> List.iter (Type.to_string %> print_endline) *)

(* let _ =
  Type.from_string ~env:Typing.initial_env "(int * int) -> (int list * int)"
  |> generalizations
  |> List.iter begin fun (subst, t) ->
    (* if Type.to_string t = "'a * 'b -> 'a * 'a" then *)
    if Type.to_string t = "'a * 'a2 -> 'a0 * 'a1" then
      (Type.to_string_raw t |> print_endline;)
    else
      (to_string (subst, t) |> print_endline;)
  end *)

(* let _ =
  Type.from_string ~env:Typing.initial_env "(int * int) list -> (int list * int list)"
  |> generalizations
  |>@ snd
  |> List.iter (Type.to_string %> print_endline) *)

(* let _ =
  Type.from_string ~env:Typing.initial_env "(bool * bool) list -> (bool list * bool list)"
  |> generalizations
  |>@ snd
  |> List.iter (Type.to_string %> print_endline) *)

(* let _ =
  shared_generalizations
    (Type.from_string ~env:Typing.initial_env "int -> int")
    (Type.from_string ~env:Typing.initial_env "string -> int")
  |> List.iter (Type.to_string %> print_endline) *)

(* let _ =
  shared_generalizations
    (Type.from_string ~env:Typing.initial_env "(int * int) list -> (int list * int list)")
    (Type.from_string ~env:Typing.initial_env "(bool * bool) list -> (bool list * bool list)")
  |> List.iter (Type.to_string %> print_endline) *)

(* let _ =
  shared_generalizations
    (Type.from_string ~env:Typing.initial_env "(int * int) list -> (int list * int list)")
    (Type.from_string ~env:Typing.initial_env "(bool * bool) list -> (bool list * bool list)")
  |>@ Type.is_equal_or_more_general_than (Type.from_string ~env:Typing.initial_env  "('a * 'a) list -> 'a list * 'a list")
  |> List.iter (string_of_bool %> print_endline) *)

(* let _ =
  print_endline "Most specific shared generalization of (int * int) list -> (int list * int list) and (bool * bool) list -> (bool list * bool list):";
  most_specific_shared_generalization_of_types
    [ (Type.from_string ~env:Typing.initial_env "(int * int) list -> (int list * int list)")
    ; (Type.from_string ~env:Typing.initial_env "(bool * bool) list -> (bool list * bool list)") ]
  |> Type.to_string |> print_endline *)

(* let _ =
  most_specific_shared_generalization_of_types
    [ (Type.from_string ~env:Typing.initial_env "int -> int")
    ; (Type.from_string ~env:Typing.initial_env "string -> int") ]
  |> Type.to_string |> print_endline *)


(* type vars in the input should generalize to *everything* *)
(* expected: int -> int *)
(* currently: we crash to force you not to do this *)
(* let _ =
  shared_generalizations
    (Type.from_string ~env:Typing.initial_env "'a -> int")
    (Type.from_string ~env:Typing.initial_env "int -> 'a")
  |> List.iter (Type.to_string %> print_endline) *)
