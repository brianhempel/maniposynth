open Parsetree

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

let concat_map f list =  List.map f list |> List.concat

(* Default for Option, like (null || default) in other languages *)
let (||&) opt default = match opt with Some x -> x | _ -> default
(* Rightward compose default for Option *)
let (%||&) f default = fun x -> match f x with Some x -> x | _ -> default

module Option = struct
  (* Selections from https://ocaml.org/api/Option.html *)
  let map f = function Some x -> Some (f x) | None -> None
  let join = function Some (Some x) -> Some x | _ -> None
  let to_list = function Some x -> [x] | None -> []

  let rec project = function
    | []             -> Some []
    | None   :: _    -> None
    | Some x :: rest -> project rest |> map (List.cons x)
end

let clamp lo hi x =
  if x < lo then lo
  else if x > hi then hi
  else x

module String = struct
  include String

  (* Like String.sub but does not error for ranges outside the string. *)
  let safe_sub i len str =
    let safe_i = clamp 0 (String.length str) i in
    let safe_j = clamp 0 (String.length str) (i + len) in
    sub str safe_i (safe_j - safe_i)

  let prefix len str = safe_sub 0 len str
  let suffix len str = safe_sub (length str - len) len str

  let drop len str = suffix (length str - len) str

  (* Tail recursive string matcher to see if target containts str at the given indices. *)
  let rec matches_at_indices_ str_i target target_i target_len str =
    if target_i >= target_len then
      true
    else if unsafe_get str str_i = unsafe_get target target_i then
      matches_at_indices_ (str_i + 1) target (target_i + 1) target_len str
    else
      false

  let matches_at_index str_i target str  =
    let str_len    = length str in
    let target_len = length target in
    if str_i < 0 || str_i > str_len - target_len then
      false
    else
      matches_at_indices_ str_i target 0 target_len str

  let starts_with prefix str =
    matches_at_index 0 prefix str

  let ends_with suffix str =
    let str_len    = length str in
    let suffix_len = length suffix in
    matches_at_index (str_len - suffix_len) suffix str

  let drop_prefix prefix str =
    if starts_with prefix str
    then drop (length prefix) str
    else str

  let find_index ?(start_index = 0) target str : int option =
    let target_len = length target in
    let last_i     = length str - target_len in
    let rec loop i =
      if i > last_i then
        None
      else if matches_at_indices_ i target 0 target_len str then
        Some i
      else
        loop (i + 1)
    in
    if last_i < 0 then
      None
    else
      loop start_index

  let rec split ?(limit = -1) ?(start_index = 0) sep str =
    if limit = 1 then
      [sub str start_index (length str - start_index)]
    else
      match find_index ~start_index sep str with
      | Some i ->
          sub str start_index (i - start_index)
          :: split ~limit:(limit - 1) ~start_index:(i + length sep) sep str
      | None ->
          [sub str start_index (length str - start_index)]

  (* let replace ~target ~replacement str =
    split target str |> String.concat replacement *)
end


(* Rightward fmap/filter on Option *)
let (|>&)  x_opt f = match x_opt with Some x -> Some (f x) | None -> None
let (|>&?) x_opt f = match x_opt with Some x -> (if f x then x_opt else None) | None -> None
(* Rightward join on Option (equiv to filter_map) *)
let (|>&&) x_opt f = x_opt |>& f |> Option.join

(* Rightward map/filter on List *)
let (|>@)  list f = List.map f list
let (|>@?) list f = List.filter f list
(* Rightward concat_map on list *)
let (|>@@) list f = concat_map f list
(* Rightward filter_map on list *)
let (|>@&) list f = list |>@ f |>@@ Option.to_list

(* Rightward composition *)
let (%>)   f g = fun x -> f x |> g
(* Rightward composition on Option *)
let (%>&)  f g = fun x -> f x |>& g
(* Rightward composition filter on Option *)
let (%>&?) f g = fun x -> f x |>&? g
(* Rightward composition join on Option *)
let (%>&&) f g = fun x -> f x |>&& g
(* Rightward compose map on List *)
let (%>@)  f g = fun x -> f x |>@ g
(* Rightward compose filter on List *)
let (%>@?) f g = fun x -> f x |>@? g
(* Rightward compose concat_map on List *)
let (%>@@) f g = fun x -> f x |>@@ g
(* Rightward compose filter_map on List *)
let (%>@&) f g = fun x -> f x |>@& g

let partition pred list =
  List.fold_right
    (fun x (trues, falses) -> if pred x then (x::trues, falses) else (trues, x::falses))
    list
    ([], [])

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
  let to_string typ = Printtyp.reset (); Formatter_to_stringifier.f Printtyp.type_expr typ
  let from_string ?(env = Env.empty) str =
    begin
      Lexing.from_string str
      |> Parse.core_type
      |> Typetexp.transl_simple_type env false
    end.ctyp_type

  (* May only need type env in case of GADTs, which we don't care about. *)
  let does_unify t1 t2 =
    try
      Ctype.unify Env.empty (Ctype.instance t1) (Ctype.instance t2);
      true
    with _ -> false

  (* Stops flattening if a labeled argument is encountered. *)
  (* e.g. 'a -> 'b -> 'c to ['a, 'b, 'c] *)
  let rec flatten_arrows typ =
    let open Types in
    match typ.desc with
    | Tarrow (Nolabel, ltype, rtype, Cok) -> ltype :: flatten_arrows rtype
    | Types.Tlink typ                     -> flatten_arrows typ
    | _                                   -> [typ]
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

  let replace_by pred node' prog =
    Node.map (fun node -> if pred node then node' else node) prog

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
  let var name =
    let loc = Loc_.fresh () in
    ident ~loc { loc = loc; txt = Longident.parse name }

  let all prog = (everything (Sis prog)).exps

  let to_string = Pprintast.string_of_expression
  let from_string = Lexing.from_string %> Parse.expression

  let ident_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_ident lid_loced -> Some lid_loced
    | _                    -> None

  let ctor_lid_loced (exp : expression) =
    match exp.pexp_desc with
    | Pexp_construct (lid_loced, _) -> Some lid_loced
    | _                             -> None
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
  let ctor_lids_loced = flatten %>@& ctor_lid_loced
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