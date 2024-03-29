open Parsetree
open Util

type program = structure_item list (* === structure *)

type everything =
  { vbs          : value_binding list
  ; exps         : expression list
  ; pats         : pattern list
  ; struct_items : structure_item list
  }

let dflt_iter   = Ast_iterator.default_iterator
let dflt_mapper = Ast_mapper.default_mapper

type node =
  | Exp of expression
  | Pat of pattern
  | Vb  of value_binding
  | Si  of structure_item
  | Sis of structure

let everything node =
  let vbs          = ref [] in
  let exps         = ref [] in
  let pats         = ref [] in
  let struct_items = ref [] in
  let iter =
    { dflt_iter
    with value_binding  = (fun iter vb  -> vbs          := vb ::!vbs;          dflt_iter.value_binding  iter vb)
    ;    expr           = (fun iter exp -> exps         := exp::!exps;         dflt_iter.expr           iter exp)
    ;    pat            = (fun iter pat -> pats         := pat::!pats;         dflt_iter.pat            iter pat)
    ;    structure_item = (fun iter si  -> struct_items := si ::!struct_items; dflt_iter.structure_item iter si)
    } in
  begin match node with
  | Exp exp  -> iter.expr           iter exp
  | Pat pat  -> iter.pat            iter pat
  | Vb  vb   -> iter.value_binding  iter vb
  | Si  si   -> iter.structure_item iter si
  | Sis prog -> iter.structure      iter prog
  end;
  { vbs            = !vbs
  ; exps           = !exps
  ; pats           = !pats
  ; struct_items   = !struct_items
  }


(* Module renamed to Loc at the end of this file. Use Loc. Has to do with dependency ordering. *)
module Loc_ = struct
  type t = Location.t

  module Pos = struct
    type t = Lexing.position

    (* Fresh positions are given new, negative values. *)
    let counter = ref 0
    let next () = decr counter; !counter
    let newloc_str = "newloc"
    let fresh () =
      Lexing.{ pos_fname = newloc_str; pos_lnum = next (); pos_bol = -1; pos_cnum = -1 }

    let to_string { Lexing.pos_fname; pos_lnum; pos_bol; pos_cnum } =
      "{ pos_fname = " ^ pos_fname ^
      "; pos_lnum = " ^ string_of_int pos_lnum ^
      "; pos_bol = " ^ string_of_int pos_bol ^
      "; pos_cnum = " ^ string_of_int pos_cnum ^ " " ^
      "}"

    let compare pos1 pos2 =
      let open Lexing in
      Pervasives.compare
        (pos1.pos_fname, pos1.pos_cnum, pos1.pos_lnum, pos1.pos_bol)
        (pos2.pos_fname, pos2.pos_cnum, pos2.pos_lnum, pos2.pos_bol)

    let byte_in_file { Lexing.pos_bol; pos_cnum; _ } =
      pos_bol + pos_cnum
  end

  (* let none = Location.none *)
  let fresh () =
    Location.{ loc_start = Pos.fresh (); loc_end = Pos.fresh (); loc_ghost = false }

  let mk txt = Location.mkloc txt (fresh ())

  let loc { Location.loc; txt = _ } = loc
  let txt { Location.txt; loc = _ } = txt

  (* Makes a fresh loc *)
  (* Use Longident.lident for Location.none *)
  let lident str = mk (Longident.Lident str)

  let to_string { Location.loc_start; loc_end; loc_ghost } =
    "{ loc_start = " ^ Pos.to_string loc_start ^
    "; loc_end = " ^ Pos.to_string loc_end ^
    "; loc_ghost = " ^ string_of_bool loc_ghost ^ " " ^
    "}"

  let compare loc1 loc2 =
    let open Location in
    match Pos.compare loc1.loc_start loc2.loc_start with
    | 0 ->
      begin match Pos.compare loc1.loc_end loc2.loc_end with
      | 0 -> Pervasives.compare loc1.loc_ghost loc2.loc_ghost
      | n -> n
      end
    | n -> n
end

module Longident = struct
  include Longident

  (* Uses Location.none *)
  (* Use Loc.ident for a fresh loc *)
  let lident str = Location.mknoloc (Lident str)

  let simple_name = function
    | Lident name -> Some name
    | _           -> None

  let to_string = flatten %> String.concat "."
end

module Type = struct
  type t = Types.type_expr

  let to_string typ = Printtyp.reset (); Formatter_to_stringifier.f Printtyp.type_expr typ
  (* let to_string_raw typ = Printtyp.reset (); Formatter_to_stringifier.f Printtyp.raw_type_expr typ *)
  let to_string_raw typ = Formatter_to_stringifier.f Printtyp.raw_type_expr typ
  let from_core_type ?(env = Env.empty) core_type = (Typetexp.transl_simple_type env false core_type).ctyp_type
  let from_string ?(env = Env.empty) str =
    Lexing.from_string str
    |> Parse.core_type
    |> from_core_type ~env
  let to_core_type = to_string %> Lexing.from_string %> Parse.core_type

  let of_exp ?(type_env = Env.empty) exp = (Typecore.type_exp type_env exp).exp_type
  let of_exp_opt ?(type_env = Env.empty) exp =
    try Some (of_exp ~type_env exp)
    with Typetexp.Error (_loc, type_env, err) ->
      Typetexp.report_error type_env Format.std_formatter err;
      None

  let copy (t : t) : t = Btype.cleanup_abbrev (); Marshal.from_bytes (Marshal.to_bytes t [Closures]) 0

  let rec iter f typ = Btype.iter_type_expr (fun t -> iter f t) typ; f typ

  let new_var () = Btype.newgenvar ()
  let tuple ts = Btype.newgenty (Ttuple ts)

  (* Follow links/substs to a regular type *)
  (* See printtyp.ml for "safe_repr" version that catches cycles *)
  let rec regular typ =
    match typ.Types.desc with
    | Types.Tlink typ
    | Types.Tsubst typ -> regular typ
    | _ -> typ

  (* For cache keying. Faster than unification. *)
  let rec equal_ignoring_id_and_scope (* ?(show = false) *) (t1 : t) (t2 : t) : bool =
    let open Types in
    (* let rec safe_repr v = function (* copied from printtyp.ml *)
      {desc = Tlink t; _} when not (List.memq t v) ->
        safe_repr (t::v) t
      | t -> t
    in *)
    let recurse = equal_ignoring_id_and_scope (* ~show *) in
    let t1 = regular t1 in
    let t2 = regular t2 in
    begin
    (* (fun b -> if not b then
      (if show then print_endline (to_string_raw t1 ^ " <> " ^ to_string_raw t2); b)
    else
      b
    ) @@ *)
    match t1.desc, t2.desc with
    | Tvar str_opt1, Tvar str_opt2
    | Tunivar str_opt1, Tunivar str_opt2 ->
      (* let p = function None -> "None" | Some str -> "Some \'" ^ str ^ "\'" in
      if show then print_endline (p str_opt1 ^ " vs " ^ p str_opt2 ^ " " ^ string_of_bool (str_opt1 = str_opt2)); *)
      t1.level = t2.level &&
      str_opt1 = str_opt2

    | Tarrow (lab1, t_l1, t_r1, comm1)
    , Tarrow (lab2, t_l2, t_r2, comm2) ->
      let rec get_comm = function Clink { contents = comm } -> get_comm comm | comm -> comm in
      lab1 = lab2 && get_comm comm1 = get_comm comm2 && recurse t_l1 t_l2 && recurse t_r1 t_r2

    | Ttuple ts1
    , Ttuple ts2 -> List.for_all2_safe recurse ts1 ts2

    | Tconstr (path1, ts1, _abbrev_memo1)
    , Tconstr (path2, ts2, _abbrev_memo2) ->
      (* if show then begin match path1, path2 with
      | Path.Pident ident1, Path.Pident ident2 -> print_endline (Formatter_to_stringifier.f Ident.print ident1 ^ " vs " ^ Formatter_to_stringifier.f Ident.print ident2 ^ " is " ^ string_of_bool (Path.same path1 path2))
      | _ -> ()
      end; *)
      Path.same path1 path2 && (
        (* if show then begin
          print_endline (string_of_bool (List.for_all2_safe recurse ts1 ts2));
          print_endline ("ts1: " ^ String.concat ", " (ts1 |>@ to_string_raw));
          print_endline ("ts2: " ^ String.concat ", " (ts2 |>@ to_string_raw));
        end; *)
        List.for_all2_safe recurse ts1 ts2
      )

    | Tobject (t1, { contents = Some (path1, ts1) })
    , Tobject (t2, { contents = Some (path2, ts2) }) ->
      recurse t1 t2 && Path.same path1 path2 && List.for_all2_safe recurse ts1 ts2

    | Tobject (t1, { contents = None })
    , Tobject (t2, { contents = None }) ->
      recurse t1 t2

    | Tobject _
    , Tobject _ -> false

    | Tfield (lab1, kind1, t1, t_rest1)
    , Tfield (lab2, kind2, t2, t_rest2) ->
      lab1 = lab2 && kind1 = kind2 && recurse t1 t2 && recurse t_rest1 t_rest2

    | Tnil
    , Tnil -> true

    | Tvariant row1
    , Tvariant row2 ->
      List.for_all2_safe begin fun (lab1, field1) (lab2, field2) ->
        lab1 = lab2 &&
        let rec row_fields_equal_ignoring_id field1 field2 =
          match field1, field2 with
          | Rpresent (Some t1), Rpresent (Some t2)-> recurse t1 t2
          | Rpresent None, Rpresent None -> true
          | Reither (bool_a1, ts1, bool_b1, { contents = Some field1 })
          , Reither (bool_a2, ts2, bool_b2, { contents = Some field2 }) ->
            bool_a1 = bool_a2 &&
            List.for_all2_safe recurse ts1 ts2 &&
            bool_b1 = bool_b2 &&
            row_fields_equal_ignoring_id field1 field2
          | Reither (bool_a1, ts1, bool_b1, { contents = None })
          , Reither (bool_a2, ts2, bool_b2, { contents = None }) ->
            bool_a1 = bool_a2 &&
            List.for_all2_safe recurse ts1 ts2 &&
            bool_b1 = bool_b2
          | Rabsent, Rabsent -> true
          | _ -> false
        in
        row_fields_equal_ignoring_id field1 field2
      end row1.row_fields row2.row_fields &&
      recurse row1.row_more row2.row_more &&
      row1.row_closed = row2.row_closed &&
      row1.row_fixed = row2.row_fixed &&
      begin match row1.row_name, row2.row_name with
      | Some (path1, ts1), Some (path2, ts2) -> Path.same path1 path2 && List.for_all2_safe recurse ts1 ts2
      | None, None -> true
      | _ -> false
      end

    | Tpoly (t1, ts1)
    , Tpoly (t2, ts2) -> recurse t1 t2 && List.for_all2_safe recurse ts1 ts2

    | Tpackage (path1, lids1, ts1)
    , Tpackage (path2, lids2, ts2) ->
      Path.same path1 path2 && List.for_all2_safe (=) lids1 lids2 && List.for_all2_safe recurse ts1 ts2

    | Tlink _, _
    | Tsubst _, _
    | _, Tlink _
    | _, Tsubst _ -> failwith "equal_ignoring_id_and_scope: shouldn't happen"

    | _ -> false
    end



  let rec is_tconstr_with_path target_path typ =
    match typ.Types.desc with
    | Types.Tconstr (path, _, _) -> path = target_path
    | Types.Tlink t
    | Types.Tsubst t -> is_tconstr_with_path target_path t
    | _ -> false
  let is_unit_type   = is_tconstr_with_path Predef.path_unit
  let is_bool_type   = is_tconstr_with_path Predef.path_bool
  let is_string_type = is_tconstr_with_path Predef.path_string
  let is_int_type    = is_tconstr_with_path Predef.path_int
  let is_char_type   = is_tconstr_with_path Predef.path_char
  let is_float_type  = is_tconstr_with_path Predef.path_float
  let is_exn_type    = is_tconstr_with_path Predef.path_exn
  let rec is_var_type typ = match typ.Types.desc with
    | Types.Tvar _
    | Types.Tunivar _ -> true
    | Types.Tlink t
    | Types.Tsubst t -> is_var_type t
    | _ -> false
  let rec is_arrow_type typ = match typ.Types.desc with
    | Types.Tarrow _ -> true
    | Types.Tlink t
    | Types.Tsubst t -> is_arrow_type t
    | _ -> false
  let rec is_ref_type typ =
    match typ.Types.desc with
    | Types.Tconstr (Path.Pdot (_, "ref", _), _, _) -> true
    | Types.Tlink t
    | Types.Tsubst t -> is_ref_type t
    | _ -> false



  let rec var_name typ = match typ.Types.desc with
    | Types.Tvar name_opt
    | Types.Tunivar name_opt -> name_opt
    | Types.Tlink t
    | Types.Tsubst t      -> var_name t
    | _                   -> None

  let rec tvar_name typ = match typ.Types.desc with
    | Types.Tvar name_opt -> name_opt
    | Types.Tlink t
    | Types.Tsubst t      -> tvar_name t
    | _                   -> None

  (* Deduplicated Tvar/Tunivar names, from left to right. *)
  let names typ =
    let names = ref [] in
    typ
    |> iter begin fun t ->
      match t.desc with
      | Types.Tvar    (Some name)
      | Types.Tunivar (Some name) -> if List.mem name !names then () else names := name :: !names
      | _                         -> ()
    end;
    List.rev !names

  (* First pass to quickly discard non-unifiable terms. *)
  let rec might_unify t1 t2 =
    let open Types in
    (* let rec safe_repr v = function (* copied from printtyp.ml *)
      {desc = Tlink t; _} when not (List.memq t v) ->
        safe_repr (t::v) t
      | t -> t
    in *)
    let recurse = might_unify in
    let t1 = regular t1 in
    let t2 = regular t2 in
    match t1.desc, t2.desc with
    | Tvar _, _
    | _, Tvar _
    | Tunivar _, _
    | _, Tunivar _ ->
      true

    | Tarrow (_lab1, t_l1, t_r1, _comm1)
    , Tarrow (_lab2, t_l2, t_r2, _comm2) ->
      recurse t_l1 t_l2 && recurse t_r1 t_r2

    | Tarrow _, _
    | _, Tarrow _ -> false

    | Ttuple ts1
    , Ttuple ts2 -> List.for_all2_safe recurse ts1 ts2

    | Ttuple _, _
    | _, Ttuple _ -> false

    | Tconstr (_path1, ts1, _abbrev_memo1)
    , Tconstr (_path2, ts2, _abbrev_memo2) ->
      List.for_all2_safe recurse ts1 ts2

    | Tconstr _, _
    | _, Tconstr _ -> false

    | Tobject _
    , Tobject _ ->
      true

    | Tobject _, _
    | _, Tobject _ -> false

    | Tfield (lab1, kind1, t1, t_rest1)
    , Tfield (lab2, kind2, t2, t_rest2) ->
      lab1 = lab2 && kind1 = kind2 && recurse t1 t2 && recurse t_rest1 t_rest2

    | Tfield _, _
    | _, Tfield _ -> false

    | Tnil
    , Tnil -> true

    | Tnil, _
    | _, Tnil -> false

    | Tvariant _
    , Tvariant _ ->
      true

    | Tvariant _, _
    | _, Tvariant _ -> false

    | Tpoly (t1, ts1)
    , Tpoly (t2, ts2) -> recurse t1 t2 && List.for_all2_safe recurse ts1 ts2

    | Tpoly _, _
    | _, Tpoly _ -> false

    | Tpackage (_path1, _lids1, ts1)
    , Tpackage (_path2, _lids2, ts2) ->
      List.for_all2_safe recurse ts1 ts2

    | Tpackage _, _
    | _, Tpackage _ -> false

    | Tlink _, _
    | Tsubst _, _ -> failwith "equal_ignoring_id_and_scope: shouldn't happen"



  (* LOOK AT ALL THIS STUFF I TRIED TO NOT MUTATE WHEN TRYING TO UNIFY/SUBTYPE! *)
  (* These all don't work. *)

    (* Ctype.generic_instance (Ctype.correct_levels t) *)
    (* Ctype.instance t *)
    (* Ctype.instance ~partial:false t *)
    (* Ctype.instance ~partial:true t *)
    (* let t' = Ctype.correct_levels t in
    Ctype.generalize t';
    t' *)
  (* let is_more_general more_general target =
    Ctype.moregeneral Env.empty true more_general target *)

  (* May only need type env in case of GADTs, which we don't care about. *)
  let does_unify t1 t2 =
    (* print_endline @@ "Unifying " ^ to_string t1 ^ "\twith " ^ to_string t2; *)
    (* Ctype.matches Env.empty t1 t2 *)
    (* is_more_general t1 t2 *)
    might_unify t1 t2 &&
    try
      (* Ctype.unify Env.empty (Ctype.generic_instance t1) (Ctype.generic_instance t2); *)
      Ctype.unify Env.empty (copy t1) (copy t2);
      true
    with
    (* | Typetexp.Error (_loc, type_env, err) ->
      Typetexp.report_error type_env Format.std_formatter err;
      false *)
    | _ ->
      (* print_endline @@ to_string t1 ^ " !~ " ^ to_string t2; *)
      false

  (* I think t1 and t2 may still be mutated even if unification fails. *)
  let unify_mutating_opt t1 t2 =
    (* print_endline @@ "Unifying " ^ to_string t1 ^ "\twith " ^ to_string t2; *)
    if not (might_unify t1 t2) then None else
    try
      Ctype.unify Env.empty t1 t2;
      Some t1
    with _ -> None

  let unify_opt t1 t2 =
    (* print_endline @@ "Unifying " ^ to_string t1 ^ "\twith " ^ to_string t2; *)
    if not (might_unify t1 t2) then None else
    let t1' = copy t1 in
    try
      Ctype.unify Env.empty t1' (copy t2);
      Some t1'
    with _ -> None

  (* Is typ1 equal or more general than typ2? *)
  let is_equal_or_more_general_than typ1 typ2 =
    (* begin fun out ->
      print_endline @@ to_string typ1 ^ "\t\t" ^ to_string typ2 ^ "\t\t" ^ (unify_opt typ1 typ2 |>& to_string ||& "-") ^ "\t\t" ^ string_of_bool out;
      out
    end @@ *)
    match unify_opt typ1 typ2 with (* Apparently, unify prefers the Tvars in typ2 *)
    | Some typ2' -> to_string typ2' = to_string typ2
    | None       -> false

  (* Stops flattening if a labeled argument is encountered. *)
  (* e.g. 'a -> 'b -> 'c to ['a, 'b, 'c] *)
  let rec flatten_arrows typ =
    let open Types in
    match typ.desc with
    | Tarrow (Nolabel, ltype, rtype, _) -> ltype :: flatten_arrows rtype
    | Tlink typ | Tsubst typ            -> flatten_arrows typ
    | _                                 -> [typ]

  (* Arg count for arrow types. (Not type arg count). *)
  (* Stops if a labeled argument is encountered. *)
  let rec arrow_arg_count typ =
    let open Types in
    match typ.desc with
    | Tarrow (Nolabel, _ltype, rtype, _) -> 1 + arrow_arg_count rtype
    | Tlink typ | Tsubst typ             -> arrow_arg_count typ
    | _                                  -> 0

  (* Stops flattening if a labeled argument is encountered. *)
  (* e.g. 'a -> 'b -> 'c to (['a, 'b], 'c) *)
  let rec args_and_ret typ =
    let open Types in
    match typ.desc with
    | Tarrow (Nolabel, ltype, rtype, Cok) -> args_and_ret rtype |> Tup2.map_fst (List.cons ltype)
    | Tlink typ | Tsubst typ              -> args_and_ret typ
    | _                                   -> ([], typ)

  let arrow t1 t2 =
    Btype.newgenty @@ Tarrow (Nolabel, t1, t2, Cok)

  let rec unflatten_arrows types =
    match types with
    | []      -> failwith "shouldn't give an empty type list to Type.unflatten_arrows"
    | [t]     -> t
    | t::rest -> arrow t (unflatten_arrows rest)

  let rec flatten typ =
    let open Types in
    let concat_map = List.concat_map in
    let rec flatten_row_field = function
    | Rpresent (Some t)                                 -> flatten t
    | Rpresent None                                     -> []
    | Reither (_, ts, _, { contents = Some row_field }) -> concat_map flatten ts @ flatten_row_field row_field
    | Reither (_, ts, _, { contents = None })           -> concat_map flatten ts
    | Rabsent                                           -> []
    in
    typ ::
    match typ.desc with
    | Tvar _                                   -> []
    | Tarrow (_, l, r, _)                      -> flatten l @ flatten r
    | Ttuple ts                                -> concat_map flatten ts
    | Tconstr (_, ts, _)                       -> concat_map flatten ts
    | Tobject (t, { contents = Some (_, ts) }) -> flatten t @ concat_map flatten ts
    | Tobject (t, { contents = None })         -> flatten t
    | Tfield (_, _, t1, t2)                    -> flatten t1 @ flatten t2
    | Tnil                                     -> []
    | Tlink t                                  -> flatten t
    | Tsubst t                                 -> flatten t
    | Tunivar _                                -> []
    | Tpoly (t, ts)                            -> concat_map flatten (t::ts)
    | Tpackage (_, _, ts)                      -> concat_map flatten ts
    | Tvariant { row_fields; row_more; row_name = Some (_, ts); _ } -> (row_fields |>@ snd |>@@ flatten_row_field) @ flatten row_more @ concat_map flatten ts
    | Tvariant { row_fields; row_more; row_name = None;         _ } -> (row_fields |>@ snd |>@@ flatten_row_field) @ flatten row_more

  (* Bottom up (children mapped before parents). *)
  (* Note that mutable refs will no longer point to their originals (replaced instead with copies). Shouldn't matter for us. *)
  let rec map f typ =
    let open Types in
    let recurse = map                                      f in
    let rec map_abbrev_memo (abbrev_memo : abbrev_memo) =
      match abbrev_memo with
      | Mnil ->
        Mnil
      | Mcons (private_flag, path, abbrev, expansion, memo) ->
        Mcons (private_flag, path, recurse abbrev, recurse expansion, map_abbrev_memo memo)
      | Mlink memo_ref ->
        Mlink { contents = map_abbrev_memo !memo_ref }
    in
    let map_row_desc { row_fields; row_more; row_bound; row_closed; row_fixed; row_name } =
      let rec map_row_field (row_field : row_field) =
        match row_field with
        | Rpresent None                                               -> row_field
        | Rpresent (Some t)                                           -> Rpresent (Some (recurse t))
        | Reither (isconst, ts, ispat, { contents = None })           -> Reither (isconst, ts |>@ recurse, ispat, { contents = None })
        | Reither (isconst, ts, ispat, { contents = Some row_field }) -> Reither (isconst, ts |>@ recurse, ispat, { contents = Some (map_row_field row_field) })
        | Rabsent                                                     -> Rabsent
      in
      {
        row_fields = row_fields |>@ (fun (name, row_field) -> (name, map_row_field row_field));
        row_more   = recurse row_more;
        row_bound  = row_bound;
        row_closed = row_closed;
        row_fixed  = row_fixed;
        row_name   = row_name |>& (fun (path, ts) -> (path, ts |>@ recurse))
      }
    in
    match typ.desc with
    | Tnil
    | Tunivar _
    | Tvar _                                      -> f typ
    | Tlink t
    | Tsubst t                                    -> f (recurse t)
    | Tarrow (lab, l, r, comm)                    -> f { typ with desc = Tarrow (lab, recurse l, recurse r, comm) }
    | Ttuple ts                                   -> f { typ with desc = Ttuple (ts |>@ recurse) }
    | Tconstr (path, ts, abbrev)                  -> f { typ with desc = Tconstr (path, ts |>@ recurse, { contents = map_abbrev_memo !abbrev }) }
    | Tobject (t, { contents = Some (path, ts) }) -> f { typ with desc = Tobject (recurse t, { contents = Some (path, ts |>@ recurse) }) }
    | Tobject (t, { contents = None })            -> f { typ with desc = Tobject (recurse t, { contents = None }) }
    | Tfield (name, fkind, t1, t2)                -> f { typ with desc = Tfield (name, fkind, recurse t1, recurse t2) }
    | Tpoly (t, ts)                               -> f { typ with desc = Tpoly (recurse t, ts |>@ recurse) }
    | Tpackage (path, lids, ts)                   -> f { typ with desc = Tpackage (path, lids, ts |>@ recurse) }
    | Tvariant row_desc                           -> f { typ with desc = Tvariant (map_row_desc row_desc) }

  let rename_all mapping typ =
    typ
    |> map begin fun typ ->
      match typ.desc with
      | Tvar    (Some str) -> (match List.assoc_opt str mapping with | Some name' -> { typ with desc = Tvar    (Some name') } | None -> typ)
      | Tunivar (Some str) -> (match List.assoc_opt str mapping with | Some name' -> { typ with desc = Tunivar (Some name') } | None -> typ)
      | _                  -> typ
    end

  let rename name name' typ =
    rename_all [(name, name')] typ
end


module Common
  (Node : sig
    type t
    val loc             : t -> Location.t
    val mapper          : (t -> t) -> Ast_mapper.mapper
    val iterator        : (t -> unit) -> Ast_iterator.iterator
    val mapper_node_f   : Ast_mapper.mapper -> (Ast_mapper.mapper -> t -> t)
    val iterator_node_f : Ast_iterator.iterator -> (Ast_iterator.iterator -> t -> unit)
  end) = struct

  (* type t = Node.t *)
  let loc = Node.loc
  let mapper = Node.mapper
  let iter f prog =
    let iterator = Node.iterator f in
    iterator.structure iterator prog
  let iterator = Node.iterator
  let apply_mapper   mapper   node = (Node.mapper_node_f   mapper)   mapper   node
  let apply_iterator iterator node = (Node.iterator_node_f iterator) iterator node


  exception Found of Node.t

  (* let map_node f = apply_mapper (mapper f) *)

  let map f struct_items =
    let mapper = Node.mapper f in
    mapper.structure mapper struct_items

  let map_by pred f prog =
    map (fun node -> if pred node then f node else node) prog

  let map_at target_loc f prog =
    map_by (loc %> (=) target_loc) f prog

  let replace_by pred node' prog =
    map_by pred (fun _ -> node') prog

  let replace target_loc = replace_by (loc %> (=) target_loc)

  let find_by pred prog : Node.t =
    try
      prog |> iter (fun node -> if pred node then raise (Found node));
      failwith "find_by: couldn't find node"
    with Found node -> node
  let find_by_opt pred prog : Node.t option =
    try
      prog |> iter (fun node -> if pred node then raise (Found node));
      None
    with Found node -> Some node

  let find     target_loc = find_by (loc %> (=) target_loc)
  let find_opt target_loc = find_by_opt (loc %> (=) target_loc)

  let exists pred prog = find_by_opt pred prog <> None

  (* Returns extracted node, and a function that takes a node and replaces that element. *)
  let extract_by pred prog : Node.t * (Node.t -> program) =
    let node = find_by pred prog in
    ( node
    , fun node' -> replace_by ((==) node) node' prog (* Physical equality (==) will work here because node is always boxed and was pulled out of prog *)
    )
  let extract_by_opt pred prog : (Node.t * (Node.t -> program)) option =
    find_by_opt pred prog |>& fun node ->
    ( node
    , fun node' -> replace_by ((==) node) node' prog (* Physical equality (==) will work here because node is always boxed and was pulled out of prog *)
    )

  let extract     target_loc = extract_by (loc %> (=) target_loc)
  let extract_opt target_loc = extract_by_opt (loc %> (=) target_loc)

  let count pred prog =
    let n = ref 0 in
    prog |> iter (fun node -> if pred node then incr n);
    !n

  (* Root element is node rather than the whole program *)
  module FromNode = struct
    let iter f root =
      let iterator = Node.iterator f in
      apply_iterator iterator root

    let map f root =
      let mapper = Node.mapper f in
      apply_mapper mapper root

    let map_by pred f root =
      map (fun node -> if pred node then f node else node) root

    let map_at target_loc f root =
      map_by (loc %> (=) target_loc) f root

    let replace_by pred node' root =
      map_by pred (fun _ -> node') root

    let replace target_loc = replace_by (loc %> (=) target_loc)

    let find_by pred root : Node.t =
      try
        root |> iter (fun node -> if pred node then raise (Found node));
        failwith "find_by: couldn't find node"
      with Found node -> node
    let find_by_opt pred root : Node.t option =
      try
        root |> iter (fun node -> if pred node then raise (Found node));
        None
      with Found node -> Some node

    let find     target_loc = find_by (loc %> (=) target_loc)
    let find_opt target_loc = find_by_opt (loc %> (=) target_loc)

    let exists pred root = find_by_opt pred root <> None

    (* Returns extracted node, and a function that takes a node and replaces that element. *)
    let extract_by pred root : Node.t * (Node.t -> Node.t) =
      let node = find_by pred root in
      ( node
      , fun node' -> replace_by ((==) node) node' root (* Physical equality (==) will work here because node is always boxed and was pulled out of root *)
      )
    let extract_by_opt pred root : (Node.t * (Node.t -> Node.t)) option =
      find_by_opt pred root |>& fun node ->
      ( node
      , fun node' -> replace_by ((==) node) node' root (* Physical equality (==) will work here because node is always boxed and was pulled out of root *)
      )

    let extract     target_loc = extract_by (loc %> (=) target_loc)
    let extract_opt target_loc = extract_by_opt (loc %> (=) target_loc)

    let count pred root =
      let n = ref 0 in
      root |> iter (fun node -> if pred node then incr n);
      !n
  end

  let child_exps node =
    let children = ref [] in
    let iter_exp_no_recurse _ e = children := e :: !children in
    let iter_once = { dflt_iter with expr = iter_exp_no_recurse } in
    (Node.iterator_node_f dflt_iter) iter_once node;
    List.rev !children (* Return the children left-to-right. *)

  let child_pats node =
    let children = ref [] in
    let iter_pat_no_recurse _ p = children := p :: !children in
    let iter_once = { dflt_iter with pat = iter_pat_no_recurse } in
    (Node.iterator_node_f dflt_iter) iter_once node;
    List.rev !children (* Return the children left-to-right. *)

  let freshen_locs node =
    let mapper = { dflt_mapper with location = (fun _ _ -> Loc_.fresh ()) } in
    apply_mapper mapper node
end

(* module Const = Ast_helper.Const *)

module Exp = struct
  include Common(struct
    type t = expression
    let loc { pexp_loc; _ } = pexp_loc
    let iterator f  =
      let iter_exp iter e = dflt_iter.expr iter e; f e in
      { dflt_iter with expr = iter_exp }
    let mapper f =
      let map_exp mapper e = f (dflt_mapper.expr mapper e) in
      { dflt_mapper with expr = map_exp }
    let mapper_node_f (mapper : Ast_mapper.mapper) = mapper.expr
    let iterator_node_f (iterator : Ast_iterator.iterator) = iterator.expr
  end)

  include Ast_helper.Exp (* Exp builders *)
  let simple_var name = (* don't parse module paths *)
    let loc = Loc_.fresh () in
    ident ~loc { loc = loc; txt = Longident.Lident name }
  let var name = (* parse module paths *)
    let loc = Loc_.fresh () in
    { (name |> Lexing.from_string |> Parse.expression) with pexp_loc = loc }
  let hole = simple_var "??"
  let simple_apply name args = apply (var name) (args |>@ fun arg -> (Asttypes.Nolabel, arg))
  let ctor name args =
    construct (Loc_.lident name) @@
    match args with
    | []    -> None
    | [arg] -> Some arg
    | args  -> Some (tuple args)
  let int_lit n = constant (Ast_helper.Const.int n)
  let string_lit str = constant (Ast_helper.Const.string str)
  let unit = construct (Longident.lident "()") None
  let apply_with_hole_args fexp n_args =  apply fexp @@ List.init n_args (fun _ -> (Asttypes.Nolabel, hole))

  let all prog = (everything (Sis prog)).exps
  let flatten exp = (everything (Exp exp)).exps

  let to_string = Pprintast.string_of_expression
  let from_string = Lexing.from_string %> Parse.expression
  let from_string_opt exp = try Some (from_string exp) with Syntaxerr.Error _ -> None

  let int (exp : expression) =
    match exp.pexp_desc with
    | Pexp_constant (Pconst_integer (int_str, None)) -> Some (int_of_string int_str)
    | _ -> None

  let string (exp : expression) =
    match exp.pexp_desc with
    | Pexp_constant (Pconst_string (str, _)) -> Some str
    | _ -> None

  let ident_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_ident lid_loced -> Some lid_loced
    | _                    -> None
  let ident_lid = ident_lid_loced %>& Loc_.txt
  let simple_name = ident_lid %>&& Longident.simple_name
  let simple_apply_parts (exp : expression) = (* No arg labels, fexp is name *)
    match exp.pexp_desc with
    | Pexp_apply (fexp, labeled_args) ->
      begin match simple_name fexp, labeled_args |>@ (function (Asttypes.Nolabel, arg) -> Some arg | _ -> None) |> Option.project with
      | Some name, Some unlabeled_args -> Some (name, unlabeled_args)
      | _                              -> None
      end
    | _ -> None
  let fexp_of_apply (exp : expression) =
    match exp.pexp_desc with
    | Pexp_apply (fexp, _) -> Some fexp
    | _                    -> None

  let body_of_fun (exp : expression) =
    match exp.pexp_desc with
    | Pexp_fun (_, _, _, body) -> Some body
    | _                        -> None

  let ctor_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_construct (lid_loced, _) -> Some lid_loced
    | _                             -> None
  let everything exp = everything (Exp exp)

  let is_unit exp =
    match ctor_lid_loced exp with
    | Some { txt = Longident.Lident "()"; _ } -> true
    | _                                       -> false
  let is_hole exp =
    match exp.pexp_desc with
    | Pexp_ident { txt = Longident.Lident "??"; _ } -> true
    | _                                             -> false
  let is_fun         = function { pexp_desc = Pexp_fun        _; _ } -> true | _ -> false
  let is_function    = function { pexp_desc = Pexp_function   _; _ } -> true | _ -> false
  let is_funlike exp = is_fun exp || is_function exp
  let is_ctor        = function { pexp_desc = Pexp_construct  _; _ } -> true | _ -> false
  let is_constant    = function { pexp_desc = Pexp_constant   _; _ } -> true | _ -> false
  let is_match       = function { pexp_desc = Pexp_match      _; _ } -> true | _ -> false
  let is_ident       = function { pexp_desc = Pexp_ident      _; _ } -> true | _ -> false
  let is_assert      = function { pexp_desc = Pexp_assert     _; _ } -> true | _ -> false
  let is_ite         = function { pexp_desc = Pexp_ifthenelse _; _ } -> true | _ -> false
  let is_simple_name = simple_name %> (<>) None
end

module Pat = struct
  include Common(struct
    type t = pattern
    let loc { ppat_loc; _ } = ppat_loc
    let iterator f =
      let iter_pat iter p = dflt_iter.pat iter p; f p in
      { dflt_iter with pat = iter_pat }
    let mapper f =
      let map_pat mapper p = f (dflt_mapper.pat mapper p) in
      { dflt_mapper with pat = map_pat }
    let mapper_node_f (mapper : Ast_mapper.mapper) = mapper.pat
    let iterator_node_f (iterator : Ast_iterator.iterator) = iterator.pat
  end)

  let all prog = (everything (Sis prog)).pats

  include Ast_helper.Pat (* Pat builders *)
  let var name =
    let loc = Loc_.fresh () in
    Ast_helper.Pat.var ~loc { loc = loc; txt = name }
  let construct_unqualified ctor_name arg = construct (Longident.lident ctor_name) arg
  let unit = construct_unqualified "()" None

  let flatten pat = (everything (Pat pat)).pats

  let to_string = Formatter_to_stringifier.f Pprintast.pattern
  let from_string = Lexing.from_string %> Parse.pattern
  let from_string_opt exp = try Some (from_string exp) with Syntaxerr.Error _ -> None

  (* let rec one_var (pat : pattern) =
    match pat.ppat_desc with
    | Ppat_var _               -> Some pat
    | Ppat_constraint (pat, _) -> one_var pat
    | _                        -> None *)

  let name_loced (pat : pattern) =
    match pat.ppat_desc with
    | Ppat_var name_loced        -> Some name_loced
    | Ppat_alias (_, name_loced) -> Some name_loced
    | _                          -> None
  let single_name (pat : pattern) =
    match pat.ppat_desc with
    | Ppat_var { txt; _ } -> Some txt
    | _                   -> None

  let ctor_lid_loced (pat : pattern) =
    match pat.ppat_desc with
    | Ppat_construct (lid_loced, _) -> Some lid_loced
    | _                             -> None

  let is_unit pat =
    match ctor_lid_loced pat with
    | Some { txt = Longident.Lident "()"; _ } -> true
    | _                                       -> false
  let is_any pat =
    match pat.ppat_desc with
    | Ppat_any -> true
    | _        -> false
  let is_catchall pat =
    match pat.ppat_desc with
    | Ppat_var _ -> true
    | Ppat_any   -> true
    | _          -> false
  let is_name        = name_loced %> (<>) None
  let is_single_name = single_name %> (<>) None

  let name            = name_loced %>& Loc_.txt
  let names_loced     = flatten %>@& name_loced
  let names           = names_loced %>@ Loc_.txt
  let ctor_lids_loced = flatten %>@& ctor_lid_loced
  let everything pat = everything (Pat pat)
end


module Case = struct
  type t = case

  let lhs       { pc_lhs;   _ } = pc_lhs
  let pat       { pc_lhs;   _ } = pc_lhs
  let guard_opt { pc_guard; _ } = pc_guard
  let rhs       { pc_rhs;   _ } = pc_rhs

  let names_loced     = pat %> Pat.names_loced
  let names           = names_loced %>@ Loc_.txt

  let map_lhs   f case = { case with pc_lhs = f case.pc_lhs }
  let map_pat          = map_lhs
  let map_guard f case = { case with pc_guard = Option.map f case.pc_guard }
  let map_rhs   f case = { case with pc_rhs = f case.pc_rhs }
end


module Vb = struct
  include Common(struct
    type t = value_binding
    let loc { pvb_loc; _ } = pvb_loc
    let iterator f =
      let iter_vb iter vb = dflt_iter.value_binding iter vb; f vb in
      { dflt_iter with value_binding = iter_vb }
    let mapper f =
      let map_vb mapper vb = f (dflt_mapper.value_binding mapper vb) in
      { dflt_mapper with value_binding = map_vb }
    let mapper_node_f (mapper : Ast_mapper.mapper) = mapper.value_binding
    let iterator_node_f (iterator : Ast_iterator.iterator) = iterator.value_binding
  end)

  let all prog = (everything (Sis prog)).vbs

  include Ast_helper.Vb (* Vb builders *)

  let to_string vb =
    Formatter_to_stringifier.f Pprintast.pattern vb.pvb_pat ^ " = " ^
    Pprintast.string_of_expression vb.pvb_expr

  (* "pat = expr" -> vb (inverse of to_string) *)
  let from_string code =
    match "let " ^ code |> Lexing.from_string |> Parse.implementation with
    | [{ pstr_desc = Pstr_value (_, [vb]); _ }] -> vb
    | struct_items                              -> failwith @@ "Vb.from_string not a vb: " ^ Pprintast.string_of_structure struct_items

  let pat { pvb_pat;  _ } = pvb_pat
  let exp { pvb_expr; _ } = pvb_expr
  let names_loced         = pat %> Pat.names_loced
  let names               = names_loced %>@ Loc_.txt

  let map_pat f vb = { vb with pvb_pat = f vb.pvb_pat }
  let map_exp f vb = { vb with pvb_expr = f vb.pvb_expr }

  (* Resolve as many names to associated expressions as possible. *)
  (* let static_bindings vb =
    let rec bind p e =
      match p.ppat_desc with
      | Ppat_any -> []
      | Ppat_var { txt = name; _ } -> [(name, e)]
      | Ppat_alias (p', { txt = name; _ }) -> (name, e) :: bind p' e
      | Ppat_constant _ -> []
      | Ppat_interval (_, _) -> []
      | Ppat_tuple ps ->


      | Ppat_construct (_, _) -> (??)
      | Ppat_variant (_, _) -> (??)
      | Ppat_record (_, _) -> (??)
      | Ppat_array _ -> (??)
      | Ppat_or (_, _) -> (??)
      | Ppat_constraint (_, _) -> (??)
      | Ppat_type _ -> (??)
      | Ppat_lazy _ -> (??)
      | Ppat_unpack _ -> (??)
      | Ppat_exception _ -> (??)
      | Ppat_extension _ -> (??)
      | Ppat_open (_, _) -> (??)
    in
    bind vb.pvb_pat vb.pvb_expr *)

  let everything vb = everything (Vb vb)
end

module VbGroups = struct
  type t = Asttypes.rec_flag * value_binding list

  let clear_empty_vb_groups struct_items =
    let map_sis mapper sis =
      dflt_mapper.structure mapper sis
      |>@? (fun si -> match si.pstr_desc with Pstr_value (_, []) -> false | _ -> true)
    in
    let map_exp mapper e =
      let e' = dflt_mapper.expr mapper e in
      match e'.pexp_desc with
      | Pexp_let (_, [], body) -> body
      | _ -> e'
    in
    let mapper = { dflt_mapper with structure = map_sis; expr = map_exp } in
    mapper.structure mapper struct_items

  (* Will also clear out any vb groups that become [] *)
  let map f struct_items =
    let map_si mapper si =
      let si' = dflt_mapper.structure_item mapper si in
      match si'.pstr_desc with
      | Pstr_value (recflag, vbs) ->
        let recflag', vbs' = f (recflag, vbs) in
        { si' with pstr_desc = Pstr_value (recflag', vbs') }
      | _ -> si'
    in
    let map_exp mapper e =
      let e' = dflt_mapper.expr mapper e in
      match e'.pexp_desc with
      | Pexp_let (recflag, vbs, body) ->
        let recflag', vbs' = f (recflag, vbs) in
        { e' with pexp_desc = Pexp_let (recflag', vbs', body) }
      | _ -> e'
    in
    let mapper = { dflt_mapper with structure_item = map_si; expr = map_exp } in
    mapper.structure mapper struct_items
    |> clear_empty_vb_groups

  let unit_vbs_to_sequence =
    (* Top-level evals are UGLY. Keep them as unit vbs. *)
    (* (The camlboot interpreter also tries to print top-level eval results) *)
    Exp.map begin fun e ->
      match e.pexp_desc with
      | Pexp_let (_, [{ pvb_pat; pvb_expr; pvb_attributes; _ }], body) when Pat.is_unit pvb_pat ->
        let e1 = { pvb_expr with pexp_attributes = pvb_attributes @ pvb_expr.pexp_attributes } in (* Copy positioning attributes from vb *)
        { e with pexp_desc = Pexp_sequence (e1, body) }
      | _ -> e
    end

  (* The user interface treat sequences as equivalent to let () = e1 in e2 *)
  module SequenceLike = struct
    let clear_empty_sequences struct_items =
      let map_sis mapper sis =
        dflt_mapper.structure mapper sis
        |>@? (fun si -> match si.pstr_desc with Pstr_eval (e, _) when Exp.is_unit e -> false | _ -> true)
      in
      let map_exp mapper e =
        let e' = dflt_mapper.expr mapper e in
        match e'.pexp_desc with
        | Pexp_sequence (e1, e2) when Exp.is_unit e1 -> e2
        | _ -> e'
      in
      let mapper = { dflt_mapper with structure = map_sis; expr = map_exp } in
      mapper.structure mapper struct_items

    (* Return None to remove the exp *)
    let map f struct_items =
      let map_si mapper si =
        let si' = dflt_mapper.structure_item mapper si in
        match si'.pstr_desc with
        | Pstr_eval (imperative_exp, attrs) ->
          let e' = f imperative_exp ||& Exp.unit in
          { si' with pstr_desc = Pstr_eval (e', attrs) }
        | _ -> si'
      in
      let map_exp mapper e =
        let e' = dflt_mapper.expr mapper e in
        match e'.pexp_desc with
        | Pexp_sequence (imperative_exp, e2) ->
          let e' = f imperative_exp ||& Exp.unit in
          { e' with pexp_desc = Pexp_sequence (e', e2) }
        | _ -> e'
      in
      let mapper = { dflt_mapper with structure_item = map_si; expr = map_exp } in
      mapper.structure mapper struct_items
      |> clear_empty_sequences
  end
end

(* Parsetree node attributes *)
(* We use these for storing visualizers and canvas positions. *)
module Attr = struct
  type t = attribute

  let name (Location.{ txt; _ }, _) = txt
  let payload (_, payload) = payload
  let exp_opt = function
    | (_, PStr [{ pstr_desc = Pstr_eval (exp, _); _}]) -> Some exp
    | _                                                -> None

  (* let exp_of_payload = function
    | PStr [{ pstr_desc = Pstr_eval (exp, _); _}] -> Some exp
    | _ -> None *)

  let findall target_name attrs =
    attrs |>@? (name %> (=) target_name)

  let findall_exp target_name attrs =
    attrs
    |>@& begin fun attr ->
      if name attr = target_name
      then exp_opt attr
      else None
    end

  let find_exp target_name attrs =
    List.hd_opt (findall_exp target_name attrs)

  let has_tag target_name attrs =
    findall target_name attrs <> []

  let add_exp target_name exp attrs =
    attrs @ [(Loc_.mk target_name, PStr [Ast_helper.Str.eval exp])]

  let add_tag target_name attrs =
    attrs @ [(Loc_.mk target_name, PStr [])]

  (* Compares exps by their unparsed representation *)
  let remove_exp target_name exp attrs =
    let target_code = Exp.to_string exp in
    attrs |>@? begin fun attr ->
      name attr <> target_name || (exp_opt attr |>& Exp.to_string) <> Some target_code
    end

  let remove_name target_name attrs =
    attrs |>@? (name %> (<>) target_name)

  let set_exp target_name exp = remove_name target_name %> add_exp target_name exp
  let set_tag target_name = remove_name target_name %> add_tag target_name
end


module Attrs = struct
  let mapper f =
    let map_attrs mapper attrs = f (dflt_mapper.attributes mapper attrs) in
    { dflt_mapper with attributes = map_attrs }

  let map f prog =
    (mapper f).structure (mapper f) prog

  let remove_all_deep_mapper = mapper (fun _ -> [])
  let remove_all_deep        = remove_all_deep_mapper.structure     remove_all_deep_mapper
  let remove_all_deep_vb     = remove_all_deep_mapper.value_binding remove_all_deep_mapper
  let remove_all_deep_exp    = remove_all_deep_mapper.expr          remove_all_deep_mapper
  let remove_all_deep_pat    = remove_all_deep_mapper.pat           remove_all_deep_mapper
end


(* Structure Items ≡ Structure (i.e. a program) *)
module StructItems = struct
  type t = structure
  let all prog = prog

  let to_string = Pprintast.string_of_structure
  let from_string = Lexing.from_string %> Parse.implementation
  let from_string_opt exp = try Some (from_string exp) with Syntaxerr.Error _ -> None

  let vb_groups sis =
    sis
    |>@& begin fun si ->
      match si.pstr_desc with
      | Pstr_value (recflag, vbs) -> Some (recflag, vbs)
      | _                         -> None
    end

  let vbs   = vb_groups %>@@ snd
  let names = vbs %>@@ Vb.names

  (* Variable names introduced or used. Excludes ctors. *)
  (* Includes endings of qualified names, e.g. "x" in Thing.x *)
  let deep_names prog =
    (* Ignore names in synth rejection attrs. *)
    let prog = Attrs.map (List.filter (Attr.name %> (<>) "not")) prog in
    let everything  = everything (Sis prog) in
    let pat_names   = everything.pats |>@& Pat.name_loced |>@ Loc_.txt in
    let ident_names = everything.exps |>@& Exp.ident_lid |>@ Longident.last in
    pat_names @ ident_names

  let map f struct_items =
    let map_sis mapper sis = f (dflt_mapper.structure mapper sis) in
    let mapper = { dflt_mapper with structure = map_sis } in
    mapper.structure mapper struct_items
end


(* Structure Item (i.e. top-level clauses) *)
module StructItem = struct
  include Common(struct
    type t = structure_item
    let loc { pstr_loc; _ } = pstr_loc
    let iterator f =
      let iter_si iter si = dflt_iter.structure_item iter si; f si in
      { dflt_iter with structure_item = iter_si }
    let mapper f =
      let map_si mapper si = f (dflt_mapper.structure_item mapper si) in
      { dflt_mapper with structure_item = map_si }
    let mapper_node_f (mapper : Ast_mapper.mapper) = mapper.structure_item
    let iterator_node_f (iterator : Ast_iterator.iterator) = iterator.structure_item
  end)

  let all prog = (everything (Sis prog)).struct_items

  include Ast_helper.Str (* Structure item builders *)

  let value_opt { pstr_desc; _ } = match pstr_desc with Pstr_value (rec_flag, vbs) -> Some (rec_flag, vbs) | _ -> None
  let vbs_opt                    = value_opt %>& snd
  let vbs_names                  = vbs_opt %>& List.concat_map Vb.names %||& []

  let to_string si = Pprintast.string_of_structure [si]
  let from_string  = StructItems.from_string %> List.hd

  (* Will search the loc of all items in a struct_items list, hand that si to f, and replace the si with the list of sis returned by f...to thereby effect removes and deletions *)
  let concat_map         f prog = StructItems.map (fun si -> si |>@@ f) prog
  let concat_map_by pred f prog = concat_map (fun si -> if pred si then f si else [si]) prog
  let concat_map_at loc' f prog = concat_map_by (loc %> (=) loc') f prog
end


module Loc = struct
  include Loc_

  let string_of_origin program loc =
    let everything = everything (Sis program) in
    let strs =
      (everything.vbs          |>@? (Vb.loc         %> (=) loc) |>@ Vb.to_string) @
      (everything.exps         |>@? (Exp.loc        %> (=) loc) |>@ Exp.to_string) @
      (everything.pats         |>@? (Pat.loc        %> (=) loc) |>@ Pat.to_string) @
      (everything.struct_items |>@? (StructItem.loc %> (=) loc) |>@ StructItem.to_string) in
    match strs with
    | []    -> to_string loc
    | [str] -> str
    | strs  -> "{{" ^ String.concat "|" strs ^ "}}"

  (* Introduction and uses of names, by loc of the name string/longindent. *)
  (* Incomplete, but this is just for debug anyway *)
  (* Mirrors binding_preservation *)
  let name_of_origin program loc =
    let everything = everything (Sis program) in
    let strs =
      (everything.pats |>@& Pat.name_loced      |>@? (Loc_.loc %> (=) loc) |>@ Loc_.txt) @
      (everything.pats |>@& Pat.ctor_lid_loced  |>@? (Loc_.loc %> (=) loc) |>@ Loc_.txt |>@ Longident.to_string) @
      (everything.exps |>@& Exp.ident_lid_loced |>@? (Loc_.loc %> (=) loc) |>@ Loc_.txt |>@ Longident.to_string) @
      (everything.exps |>@& Exp.ctor_lid_loced  |>@? (Loc_.loc %> (=) loc) |>@ Loc_.txt |>@ Longident.to_string)
    in
    match strs with
    | []    -> to_string loc
    | [str] -> str
    | strs  -> "{{" ^ String.concat "|" strs ^ "}}"
end