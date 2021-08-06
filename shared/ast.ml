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
    let fresh () =
      Lexing.{ pos_fname = "newloc"; pos_lnum = next (); pos_bol = -1; pos_cnum = -1 }

    let to_string { Lexing.pos_fname; pos_lnum; pos_bol; pos_cnum } =
      "{ pos_fname = " ^ pos_fname ^
      "; pos_lnum = " ^ string_of_int pos_lnum ^
      "; pos_bol = " ^ string_of_int pos_bol ^
      "; pos_cnum = " ^ string_of_int pos_cnum ^ " " ^
      "}"
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

  let compare = compare
end

module Longident = struct
  include Longident

  (* Uses Location.none *)
  (* Use Loc.ident for a fresh loc *)
  let lident str = Location.mknoloc (Lident str)

  let to_string = flatten %> String.concat "."
end

module Type = struct
  type t = Types.type_expr

  let to_string typ = Printtyp.reset (); Formatter_to_stringifier.f Printtyp.type_expr typ
  (* let to_string_raw typ = Printtyp.reset (); Formatter_to_stringifier.f Printtyp.raw_type_expr typ *)
  let to_string_raw typ = Formatter_to_stringifier.f Printtyp.raw_type_expr typ
  let from_string ?(env = Env.empty) str =
    begin
      Lexing.from_string str
      |> Parse.core_type
      |> Typetexp.transl_simple_type env false
    end.ctyp_type

  let of_exp ?(type_env = Env.empty) exp = (Typecore.type_exp type_env exp).exp_type
  let of_exp_opt ?(type_env = Env.empty) exp =
    try Some (of_exp ~type_env exp)
    with Typetexp.Error (_loc, type_env, err) ->
      Typetexp.report_error type_env Format.std_formatter err;
      None

  let copy (t : t) : t = Btype.cleanup_abbrev (); Marshal.from_bytes (Marshal.to_bytes t [Closures]) 0

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
    t1.level = t2.level &&
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
      str_opt1 = str_opt2

    | Tarrow (lab1, t_l1, t_r1, comm1)
    , Tarrow (lab2, t_l2, t_r2, comm2) -> lab1 = lab2 && comm1 = comm2 && recurse t_l1 t_l2 && recurse t_r1 t_r2

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

    | Tlink t1, _
    | Tsubst t1, _ -> recurse t1 t2
    | _, Tlink t2
    | _, Tsubst t2 -> recurse t1 t2

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

    | _ -> false
    end



  let rec is_tconstr_with_path target_path typ =
    match typ.Types.desc with
    | Types.Tconstr (path, _, _) -> path = target_path
    | Types.Tlink t
    | Types.Tsubst t -> is_tconstr_with_path target_path t
    | _ -> false
  let is_unit_type = is_tconstr_with_path Predef.path_unit
  let is_exn_type =  is_tconstr_with_path Predef.path_exn
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
    (* Ctype.matches Env.empty t1 t2 *)
    (* is_more_general t1 t2 *)
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
    try
      Ctype.unify Env.empty t1 t2;
      Some t1
    with _ -> None

  let unify_opt t1 t2 =
    let t1' = copy t1 in
    try
      Ctype.unify Env.empty t1' (copy t2);
      Some t1'
    with _ -> None

  (* Stops flattening if a labeled argument is encountered. *)
  (* e.g. 'a -> 'b -> 'c to ['a, 'b, 'c] *)
  let rec flatten_arrows typ =
    let open Types in
    match typ.desc with
    | Tarrow (Nolabel, ltype, rtype, Cok) -> ltype :: flatten_arrows rtype
    | Tlink typ | Tsubst typ              -> flatten_arrows typ
    | _                                   -> [typ]

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
end


module Common
  (Node : sig
    type t
    val loc : t -> Location.t
    val iter : (t -> unit) -> program -> unit
    val map : (t -> t) -> program -> program
    val iter_dflt : Ast_iterator.iterator -> t -> unit
  end) = struct

  (* type t = Node.t *)
  let loc = Node.loc
  let iter = Node.iter
  let map = Node.map

  exception Found of Node.t

  let map_by pred f prog =
    map (fun node -> if pred node then f node else node) prog

  let map_by_loc target_loc f prog =
    map_by (loc %> (=) target_loc) f prog

  let replace_by pred node' prog =
    map_by pred (fun _ -> node') prog

  let replace target_loc = replace_by (loc %> (=) target_loc)

  let find_by pred prog : Node.t =
    try
      prog |> iter (fun node -> if pred node then raise (Found node));
      failwith "find_by: couldn't find node"
    with Found node -> node

  (* Returns extracted node, and a function that takes a node and replaces that element. *)
  let extract_by pred prog : Node.t * (Node.t -> program) =
    let node = find_by pred prog in
    ( node
    , fun node' -> replace_by ((==) node) node' prog (* Physical equality (==) will work here because node is always boxed and was pulled out of prog *)
    )

  let extract target_loc = extract_by (loc %> (=) target_loc)

  let child_exps t =
    let children = ref [] in
    let iter_exp_no_recurse _ e = children := e :: !children in
    let iter_once = { dflt_iter with expr = iter_exp_no_recurse } in
    Node.iter_dflt iter_once t;
    List.rev !children (* Return the children left-to-right. *)

  let child_pats t =
    let children = ref [] in
    let iter_pat_no_recurse _ p = children := p :: !children in
    let iter_once = { dflt_iter with pat = iter_pat_no_recurse } in
    Node.iter_dflt iter_once t;
    List.rev !children (* Return the children left-to-right. *)
end

(* module Const = Ast_helper.Const *)

module Exp = struct
  include Common(struct
    type t = expression
    let loc { pexp_loc; _ } = pexp_loc
    let iter f struct_items =
      let iter_exp iter e = dflt_iter.expr iter e; f e in
      let iter = { dflt_iter with expr = iter_exp } in
      iter.structure iter struct_items
    let map f struct_items =
      let map_exp mapper e = f (dflt_mapper.expr mapper e) in
      let mapper = { dflt_mapper with expr = map_exp } in
      mapper.structure mapper struct_items
    let iter_dflt = dflt_iter.expr
  end)

  include Ast_helper.Exp (* Exp builders *)
  let simple_var name = (* don't parse module paths *)
    let loc = Loc_.fresh () in
    ident ~loc { loc = loc; txt = Longident.Lident name }
  let var name = (* parse module paths *)
    let loc = Loc_.fresh () in
    { (name |> Lexing.from_string |> Parse.expression) with pexp_loc = loc }
  let hole = simple_var "??"
  let ctor name args =
    construct (Loc_.lident name) @@
    match args with
    | []    -> None
    | [arg] -> Some arg
    | args  -> Some (tuple args)
  let int_lit n = constant (Ast_helper.Const.int n)
  let string_lit str = constant (Ast_helper.Const.string str)
  let unit = construct (Longident.lident "()") None

  let all prog = (everything (Sis prog)).exps
  let flatten exp = (everything (Exp exp)).exps

  let to_string = Pprintast.string_of_expression
  let from_string = Lexing.from_string %> Parse.expression

  let int (exp : expression) =
    match exp.pexp_desc with
    | Pexp_constant (Pconst_integer (int_str, None)) -> Some (int_of_string int_str)
    | _ -> None

  let ident_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_ident lid_loced -> Some lid_loced
    | _                    -> None
  let ident_lid = ident_lid_loced %>& Loc_.txt
  let ctor_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_construct (lid_loced, _) -> Some lid_loced
    | _                             -> None

  let is_unit exp =
    match ctor_lid_loced exp with
    | Some { txt = Longident.Lident "()"; _ } -> true
    | _                                       -> false
  let is_hole exp =
    match exp.pexp_desc with
    | Pexp_ident { txt = Longident.Lident "??"; _ } -> true
    | _                                             -> false
  let is_fun         = function { pexp_desc = Pexp_fun _; _ }      -> true | _ -> false
  let is_function    = function { pexp_desc = Pexp_function _; _ } -> true | _ -> false
  let is_funlike exp = is_fun exp || is_function exp
  let is_constant    = function { pexp_desc = Pexp_constant _; _ } -> true | _ -> false
  let is_match       = function { pexp_desc = Pexp_match _; _ }    -> true | _ -> false

  let freshen_locs exp =
    let mapper = { dflt_mapper with location = (fun _ _ -> Loc_.fresh ()) } in
    mapper.expr mapper exp

end

module Pat = struct
  include Common(struct
    type t = pattern
    let loc { ppat_loc; _ } = ppat_loc
    let iter f struct_items =
      let iter_pat iter p = dflt_iter.pat iter p; f p in
      let iter = { dflt_iter with pat = iter_pat } in
      iter.structure iter struct_items
    let map f struct_items =
      let map_pat mapper p = f (dflt_mapper.pat mapper p) in
      let mapper = { dflt_mapper with pat = map_pat } in
      mapper.structure mapper struct_items
    let iter_dflt = dflt_iter.pat
  end)

  let all prog = (everything (Sis prog)).pats

  include Ast_helper.Pat (* Pat builders *)
  let var name =
    let loc = Loc_.fresh () in
    Ast_helper.Pat.var ~loc { loc = loc; txt = name }
  let unit = construct (Longident.lident "()") None

  let flatten pat = (everything (Pat pat)).pats

  let to_string = Formatter_to_stringifier.f Pprintast.pattern
  let from_string = Lexing.from_string %> Parse.pattern
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
  let is_name        = name_loced %> (<>) None
  let is_single_name = single_name %> (<>) None

  let name            = name_loced %>& Loc_.txt
  let names_loced     = flatten %>@& name_loced
  let names           = names_loced %>@ Loc_.txt
  let ctor_lids_loced = flatten %>@& ctor_lid_loced
end


module Case = struct
  type t = case

  let rhs       { pc_rhs;   _ } = pc_rhs
  let lhs       { pc_lhs;   _ } = pc_lhs
  let pat       { pc_lhs;   _ } = pc_lhs
  let guard_opt { pc_guard; _ } = pc_guard

  let names_loced     = pat %> Pat.names_loced
  let names           = names_loced %>@ Loc_.txt
end


module Vb = struct
  include Common(struct
    type t = value_binding
    let loc { pvb_loc; _ } = pvb_loc
    let iter f struct_items =
      let iter_vb iter vb = dflt_iter.value_binding iter vb; f vb in
      let iter = { dflt_iter with value_binding = iter_vb } in
      iter.structure iter struct_items
    let map f struct_items =
      let map_vb mapper vb = f (dflt_mapper.value_binding mapper vb) in
      let mapper = { dflt_mapper with value_binding = map_vb } in
      mapper.structure mapper struct_items
    let iter_dflt = dflt_iter.value_binding
  end)

  let all prog = (everything (Sis prog)).vbs

  include Ast_helper.Vb (* Vb builders *)

  let to_string vb =
    Formatter_to_stringifier.f Pprintast.pattern vb.pvb_pat ^ " = " ^
    Pprintast.string_of_expression vb.pvb_expr

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
end

module VbGroups = struct
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

(* Structure Item (i.e. top-level clauses) *)
module StructItem = struct
  type t = structure_item
  let all prog = (everything (Sis prog)).struct_items
  let loc { pstr_loc; _ } = pstr_loc

  include Ast_helper.Str (* Structure item builders *)

  let value_opt { pstr_desc; _ } = match pstr_desc with Pstr_value (rec_flag, vbs) -> Some (rec_flag, vbs) | _ -> None
  let vbs_opt                    = value_opt %>& snd

  (* let name_loced { pstr_desc; _ } =
    match pstr_desc with
    | Pstr_eval (_, _) -> (??)
    | Pstr_value (_, _) -> (??)
    | Pstr_primitive value_desc -> Some value_desc.pval_name
    | Pstr_type (_, _) -> (??)
    | Pstr_typext _ -> (??)
    | Pstr_exception _ -> (??)
    | Pstr_module _ -> (??)
    | Pstr_recmodule _ -> (??)
    | Pstr_modtype _ -> (??)
    | Pstr_open _ -> (??)
    | Pstr_class _ -> (??)
    | Pstr_class_type _ -> (??)
    | Pstr_include _ -> (??)
    | Pstr_attribute _ -> (??)
    | Pstr_extension (_, _) -> (??) *)

  let to_string si = Pprintast.string_of_structure [si]

  let map f struct_items =
    let map_si mapper si = f (dflt_mapper.structure_item mapper si) in
    let mapper = { dflt_mapper with structure_item = map_si } in
    mapper.structure mapper struct_items
end


(* Structure Items ≡ Structure (i.e. a program) *)
module StructItems = struct
  type t = structure
  let all prog = prog

  let to_string = Pprintast.string_of_structure
  let from_string = Lexing.from_string %> Parse.implementation

  (* Variable names introduced or used. Excludes ctors. *)
  (* Includes endings of qualified names, e.g. "x" in Thing.x *)
  let names prog =
    let everything = everything (Sis prog) in
    let pat_names = everything.pats |>@& Pat.name_loced |>@ Loc_.txt in
    let ident_names = everything.exps |>@& Exp.ident_lid |>@ Longident.last in
    pat_names @ ident_names

  let map f struct_items =
    let map_sis mapper sis = f (dflt_mapper.structure mapper sis) in
    let mapper = { dflt_mapper with structure = map_sis } in
    mapper.structure mapper struct_items
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

  let add_exp target_name exp attrs =
    attrs @ [(Loc_.mk target_name, PStr [Ast_helper.Str.eval exp])]

  (* Compares exps by their unparsed representation *)
  let remove_exp target_name exp attrs =
    let target_code = Exp.to_string exp in
    attrs |>@? begin fun attr ->
      name attr <> target_name || (exp_opt attr |>& Exp.to_string) <> Some target_code
    end

  let remove_name target_name attrs =
    attrs |>@? (name %> (<>) target_name)

  let set_exp target_name exp = remove_name target_name %> add_exp target_name exp
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