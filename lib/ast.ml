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
  let                               iter =
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

let join_opt x_opt_opt = match x_opt_opt with Some (Some x) -> Some x | _ -> None
let list_of_opt = function Some x -> [x] | None -> []

(* Rightward fmap/filter on Option *)
let (|>&)  x_opt f = match x_opt with Some x -> Some (f x) | None -> None
let (|>&?) x_opt f = match x_opt with Some x -> (if f x then x_opt else None) | None -> None
(* Rightward join on Option (equiv to filter_map) *)
let (|>&&) x_opt f = x_opt |>& f |> join_opt

(* Rightward map/filter on List *)
let (|>@)  list f = List.map f list
let (|>@?) list f = List.filter f list
(* Rightward concat_map on list *)
let (|>@@) list f = concat_map f list
(* Rightward filter_map on list *)
let (|>@&) list f = list |>@ f |>@@ list_of_opt

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


module Loc = struct
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

  let to_string { Location.loc_start; loc_end; loc_ghost } =
    "{ loc_start = " ^ Pos.to_string loc_start ^
    "; loc_end = " ^ Pos.to_string loc_end ^
    "; loc_ghost = " ^ string_of_bool loc_ghost ^ " " ^
    "}"
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
  let var name = ident (Loc.mk @@ Longident.parse name)

  let all prog = (everything (Sis prog)).exps
end


module Vb = struct
  type t = value_binding
  let all prog = (everything (Sis prog)).vbs
  let loc { pvb_loc; _ } = pvb_loc

  include Ast_helper.Vb (* Vb builders *)

  let pat { pvb_pat; _ } = pvb_pat
end

module Pat = struct
  type t = pattern
  let all prog = (everything (Sis prog)).pats
  let loc { ppat_loc; _ } = ppat_loc

  include Ast_helper.Pat (* Pat builders *)
  let var name = Ast_helper.Pat.var (Loc.mk name)

  let flatten pat = (everything (Pat pat)).pats
  (* let rec one_var (pat : pattern) =
    match pat.ppat_desc with
    | Ppat_var _               -> Some pat
    | Ppat_constraint (pat, _) -> one_var pat
    | _                        -> None *)
end

(* Structure Item (i.e. top-level clauses) *)
module StructItem = struct
  type t = structure_item
  let all prog = (everything (Sis prog)).struct_items
  let loc { pstr_loc; _ } = pstr_loc

  include Ast_helper.Str (* Structure item builders *)

  let value { pstr_desc; _ } = match pstr_desc with Pstr_value (rec_flag, vbs) -> Some (rec_flag, vbs) | _ -> None

  let map f struct_items =
    let map_si mapper si = f (dflt_mapper.structure_item mapper si) in
    let mapper = { dflt_mapper with structure_item = map_si } in
    mapper.structure mapper struct_items
end


(* Structure Items ≡ Structure (i.e. a program) *)
module StructItems = struct
  type t = structure
  let all prog = prog

  let map f struct_items =
    let map_sis mapper sis = f (dflt_mapper.structure mapper sis) in
    let mapper = { dflt_mapper with structure = map_sis } in
    mapper.structure mapper struct_items
end
