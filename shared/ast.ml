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

  let to_string { Location.loc_start; loc_end; loc_ghost } =
    "{ loc_start = " ^ Pos.to_string loc_start ^
    "; loc_end = " ^ Pos.to_string loc_end ^
    "; loc_ghost = " ^ string_of_bool loc_ghost ^ " " ^
    "}"

  let compare = compare
end

module Longident = struct
  include Longident

  let to_string = flatten %> String.concat "."
end

module Type = struct
  type t = Types.type_expr

  let to_string typ = Printtyp.reset (); Formatter_to_stringifier.f Printtyp.type_expr typ
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

  let copy (t : t) : t = Marshal.from_bytes (Marshal.to_bytes t [Closures]) 0

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

  (* Stops flattening if a labeled argument is encountered. *)
  (* e.g. 'a -> 'b -> 'c to ['a, 'b, 'c] *)
  let rec flatten_arrows typ =
    let open Types in
    match typ.desc with
    | Tarrow (Nolabel, ltype, rtype, Cok) -> ltype :: flatten_arrows rtype
    | Types.Tlink typ                     -> flatten_arrows typ
    | _                                   -> [typ]

  let rec flatten typ =
    let open Types in
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

  (* Follow links/substs to a regular type *)
  let rec regular typ =
    match typ.Types.desc with
    | Types.Tlink typ
    | Types.Tsubst typ -> regular typ
    | _ -> typ
end


module Common
  (Node : sig
    type t
    val loc : t -> Location.t
    val iter : (t -> unit) -> program -> unit
    val map : (t -> t) -> program -> program
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
  end)

  include Ast_helper.Exp (* Exp builders *)
  let simple_var name = (* don't parse module paths *)
    let loc = Loc_.fresh () in
    ident ~loc { loc = loc; txt = Longident.Lident name }
  let var name = (* parse module paths *)
    let loc = Loc_.fresh () in
    { (name |> Lexing.from_string |> Parse.expression) with pexp_loc = loc }
  let int_lit n = constant (Ast_helper.Const.int n)
  let string_lit str = constant (Ast_helper.Const.string str)

  let all prog = (everything (Sis prog)).exps
  let flatten exp = (everything (Exp exp)).exps

  let to_string = Pprintast.string_of_expression
  let from_string = Lexing.from_string %> Parse.expression

  let ident_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_ident lid_loced -> Some lid_loced
    | _                    -> None
  let ident_lid = ident_lid_loced %>& Loc_.txt
  let ctor_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_construct (lid_loced, _) -> Some lid_loced
    | _                             -> None

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
  end)

  let all prog = (everything (Sis prog)).pats

  include Ast_helper.Pat (* Pat builders *)
  let var name =
    let loc = Loc_.fresh () in
    Ast_helper.Pat.var ~loc { loc = loc; txt = name }

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

  let ctor_lid_loced (pat : pattern) =
    match pat.ppat_desc with
    | Ppat_construct (lid_loced, _) -> Some lid_loced
    | _                             -> None

  let names_loced     = flatten %>@& name_loced
  let names           = names_loced %>@ Loc_.txt
  let ctor_lids_loced = flatten %>@& ctor_lid_loced
end

module Vb = struct
  type t = value_binding
  let all prog = (everything (Sis prog)).vbs
  let loc { pvb_loc; _ } = pvb_loc

  include Ast_helper.Vb (* Vb builders *)

  let to_string vb =
    Formatter_to_stringifier.f Pprintast.pattern vb.pvb_pat ^ " = " ^
    Pprintast.string_of_expression vb.pvb_expr

  let pat { pvb_pat;  _ } = pvb_pat
  let exp { pvb_expr; _ } = pvb_expr
  let names_loced         = pat %> Pat.names_loced
  let names               = names_loced %>@ Loc_.txt

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

(* Structure Item (i.e. top-level clauses) *)
module StructItem = struct
  type t = structure_item
  let all prog = (everything (Sis prog)).struct_items
  let loc { pstr_loc; _ } = pstr_loc

  include Ast_helper.Str (* Structure item builders *)

  let value { pstr_desc; _ } = match pstr_desc with Pstr_value (rec_flag, vbs) -> Some (rec_flag, vbs) | _ -> None

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

  let map f struct_items =
    let map_sis mapper sis = f (dflt_mapper.structure mapper sis) in
    let mapper = { dflt_mapper with structure = map_sis } in
    mapper.structure mapper struct_items
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