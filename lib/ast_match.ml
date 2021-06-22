open Parsetree

module SMap = Map.Make(String)

exception Match_fail

type t =
  { exps         : expression     SMap.t
  ; pats         : pattern        SMap.t
  ; vbs          : value_binding  SMap.t
  ; struct_items : structure_item SMap.t
  }

let empty_match                    = { exps                     = SMap.empty; pats = SMap.empty; vbs = SMap.empty; struct_items = SMap.empty }
let add_exp name e match_          = { match_ with exps         = SMap.add name e match_.exps }
let add_pat name p match_          = { match_ with pats         = SMap.add name p match_.pats }
let add_vb name vb match_          = { match_ with vbs          = SMap.add name vb match_.vbs }
let add_struct_item name si match_ = { match_ with struct_items = SMap.add name si match_.struct_items }
let merge_matches m1 m2 = (* m1 prefered on duplicates, but who would make a matcher with duplicate names? *)
  { exps         = SMap.union (fun _ v _ -> Some v) m1.exps         m2.exps
  ; pats         = SMap.union (fun _ v _ -> Some v) m1.pats         m2.pats
  ; vbs          = SMap.union (fun _ v _ -> Some v) m1.vbs          m2.vbs
  ; struct_items = SMap.union (fun _ v _ -> Some v) m1.struct_items m2.struct_items
  }

let list_of_opt = Util.Option.to_list

let match_all match_f mlist list =
  try List.fold_right2 (fun mitem item m -> merge_matches (match_f mitem item) m) mlist list empty_match
  with Invalid_argument _ -> raise Match_fail

(* Use node attribute names as match binding names *)
let name_self add_f node (attrs : attribute list) match_ : t =
  List.fold_right (fun ({Location.txt = name; _}, _) m -> add_f name node m) attrs match_

let match_fields match_val_f mfields fields =
  let field_lid ({Location.txt = lid; _}, _) = lid in
  let field_v (_, v) = v in
  let match_field mf f match_ =
    if field_lid mf <> field_lid f then raise Match_fail;
    merge_matches (match_val_f (field_v mf) (field_v f)) match_
  in
  let comp_names f1 f2 = compare (field_lid f1) (field_lid f2) in
  try List.fold_right2 match_field (List.sort comp_names mfields) (List.sort comp_names fields) empty_match
  with Invalid_argument _ -> raise Match_fail

let rec match_exp_ mexp exp =
  let match_exp_opt mexp_opt exp_opt = match_exps (list_of_opt mexp_opt) (list_of_opt exp_opt) in
  let match_case mcase case =
    let pat_match   = match_pat     mcase.pc_lhs   case.pc_lhs in
    let guard_match = match_exp_opt mcase.pc_guard case.pc_guard in
    let exp_match   = match_exp_    mcase.pc_rhs   case.pc_rhs in
    merge_matches pat_match (merge_matches guard_match exp_match) in
  let match_arg (mlabel, mexp) (label, exp) =
    if mlabel <> label then raise Match_fail;
    match_exp_ mexp exp in
  add_exp "root" exp @@
  name_self add_exp exp mexp.pexp_attributes @@
  match mexp.pexp_desc with
  (* | Pexp_extension ({txt = name; _}, PStr [])     -> add_exp name exp empty_match *)
  (* | Pexp_extension ({txt = _; _}, _)              -> failwith "Why does your matcher pattern have a Pexp_extension with a payload?" *)
  | Pexp_extension ({txt = _; _}, _)              -> failwith "Matcher's aren't using Pexp_extension right now"
  (* | Pexp_extension ({txt = _; _}, _)              -> failwith "Why does your matcher pattern have a Pexp_extension with a payload?" *)
  (* | Pexp_ident {txt = mlid; _}                    -> (match exp.pexp_desc with Pexp_ident {txt = lid; _} when mlid   = lid   -> empty_match | _ -> raise Match_fail) *)
  | Pexp_ident {txt = Lident name; _}             -> add_exp name exp empty_match
  | Pexp_ident {txt = _; _}                       -> failwith "if you want to match a literal var, well, you can't yet"
  | Pexp_constant mconst                          -> (match exp.pexp_desc with Pexp_constant const       when mconst = const -> empty_match | _ -> raise Match_fail)
  | Pexp_let (mrec_flag, mvbs, me)                ->
    begin match exp.pexp_desc with
      | Pexp_let (rec_flag, vbs, e) when mrec_flag = rec_flag ->
        let vbs_match = match_vbs mvbs vbs in
        let e_match   = match_exp_ me e in
        merge_matches vbs_match e_match
      | _ -> raise Match_fail
    end
  | Pexp_function mcases                          -> (match exp.pexp_desc with Pexp_function cases -> match_all match_case mcases cases | _ -> raise Match_fail)
  | Pexp_fun (mlabel, mexp_opt, mpat, mexp)       ->
    begin match exp.pexp_desc with
      | Pexp_fun (label, exp_opt, pat, exp) when mlabel = label ->
        let defaults_match = match_exp_opt mexp_opt exp_opt in
        let pat_match = match_pat mpat pat in
        let exp_match = match_exp_ mexp exp in
        merge_matches defaults_match (merge_matches pat_match exp_match)
      | _ -> raise Match_fail
    end
  | Pexp_apply (mexp, margs)                      -> (match exp.pexp_desc with Pexp_apply (exp, args)                                       -> merge_matches (match_exp_ mexp exp) (match_all match_arg margs args)                     | _ -> raise Match_fail)
  | Pexp_match (mexp, mcases)                     -> (match exp.pexp_desc with Pexp_match (exp, cases)                                      -> merge_matches (match_exp_ mexp exp) (match_all match_case mcases cases)                  | _ -> raise Match_fail)
  | Pexp_try (mexp, mcases)                       -> (match exp.pexp_desc with Pexp_try (exp, cases)                                        -> merge_matches (match_exp_ mexp exp) (match_all match_case mcases cases)                  | _ -> raise Match_fail)
  | Pexp_tuple mexps                              -> (match exp.pexp_desc with Pexp_tuple exps                                              -> match_exps mexps exps                                                                    | _ -> raise Match_fail)
  | Pexp_construct ({txt = mlid; _}, Some exp)    -> (match exp.pexp_desc with Pexp_construct ({txt = lid; _}, Some exp)  when mlid = lid   -> match_exp_ mexp exp                                                                      | _ -> raise Match_fail)
  | Pexp_construct ({txt = mlid; _}, None)        -> (match exp.pexp_desc with Pexp_construct ({txt = lid; _}, None)      when mlid = lid   -> empty_match                                                                              | _ -> raise Match_fail)
  | Pexp_variant (mstr, Some exp)                 -> (match exp.pexp_desc with Pexp_variant (str, Some exp)               when mstr = str   -> match_exp_ mexp exp                                                                      | _ -> raise Match_fail)
  | Pexp_variant (mstr, None)                     -> (match exp.pexp_desc with Pexp_variant (str, None)                   when mstr = str   -> empty_match                                                                              | _ -> raise Match_fail)
  | Pexp_record (mfields, Some mexp)              -> (match exp.pexp_desc with Pexp_record (fields, Some exp)                               -> merge_matches (match_fields match_exp_ mfields fields) (match_exp_ mexp exp)             | _ -> raise Match_fail)
  | Pexp_record (mfields, None)                   -> (match exp.pexp_desc with Pexp_record (fields, None)                                   -> match_fields match_exp_ mfields fields                                                   | _ -> raise Match_fail)
  | Pexp_field (mexp, {txt = mlid; _})            -> (match exp.pexp_desc with Pexp_field (exp, {txt = lid; _})           when mlid = lid   -> match_exp_ mexp exp                                                                      | _ -> raise Match_fail)
  | Pexp_setfield (mexp1, {txt = mlid; _}, mexp2) -> (match exp.pexp_desc with Pexp_setfield (exp1, {txt = lid; _}, exp2) when mlid = lid   -> match_exps [mexp1; mexp2] [exp1; exp2]                                                   | _ -> raise Match_fail)
  | Pexp_array mexps                              -> (match exp.pexp_desc with Pexp_array exps                                              -> match_exps mexps exps                                                                    | _ -> raise Match_fail)
  | Pexp_ifthenelse (mexp1, mexp2, None)          -> (match exp.pexp_desc with Pexp_ifthenelse (exp1, exp2, None)                           -> match_exps [mexp1; mexp2] [exp1; exp2]                                                   | _ -> raise Match_fail)
  | Pexp_ifthenelse (mexp1, mexp2, Some mexp3)    -> (match exp.pexp_desc with Pexp_ifthenelse (exp1, exp2, Some exp3)                      -> match_exps [mexp1; mexp2; mexp3] [exp1; exp2; exp3]                                      | _ -> raise Match_fail)
  | Pexp_sequence (mexp1, mexp2)                  -> (match exp.pexp_desc with Pexp_sequence (exp1, exp2)                                   -> match_exps [mexp1; mexp2] [exp1; exp2]                                                   | _ -> raise Match_fail)
  | Pexp_while (mexp1, mexp2)                     -> (match exp.pexp_desc with Pexp_while (exp1, exp2)                                      -> match_exps [mexp1; mexp2] [exp1; exp2]                                                   | _ -> raise Match_fail)
  | Pexp_for (mpat, mexp1, mexp2, mflag, mexp3)   -> (match exp.pexp_desc with Pexp_for (pat, exp1, exp2, flag, exp3)     when mflag = flag -> merge_matches (match_pat mpat pat) (match_exps [mexp1; mexp2; mexp3] [exp1; exp2; exp3]) | _ -> raise Match_fail)
  | Pexp_assert mexp                              -> (match exp.pexp_desc with Pexp_assert exp                                              -> match_exp_ mexp exp                                                                      | _ -> raise Match_fail)
  | Pexp_lazy mexp                                -> (match exp.pexp_desc with Pexp_lazy exp                                                -> match_exp_ mexp exp                                                                      | _ -> raise Match_fail)
  | Pexp_unreachable                              -> (match exp.pexp_desc with Pexp_unreachable                                             -> empty_match                                                                              | _ -> raise Match_fail)
  | Pexp_constraint (_, _)                        -> failwith "Matchers don't support Pexp_constraint"
  | Pexp_coerce (_, _, _)                         -> failwith "Matchers don't support Pexp_coerce"
  | Pexp_send (_, _)                              -> failwith "Matchers don't support Pexp_send"
  | Pexp_new _                                    -> failwith "Matchers don't support Pexp_new"
  | Pexp_setinstvar (_, _)                        -> failwith "Matchers don't support Pexp_setinstvar"
  | Pexp_override _                               -> failwith "Matchers don't support Pexp_override"
  | Pexp_letmodule (_, _, _)                      -> failwith "Matchers don't support Pexp_letmodule"
  | Pexp_letexception (_, _)                      -> failwith "Matchers don't support Pexp_letexception"
  | Pexp_poly (_, _)                              -> failwith "Matchers don't support Pexp_poly"
  | Pexp_object _                                 -> failwith "Matchers don't support Pexp_object"
  | Pexp_newtype (_, _)                           -> failwith "Matchers don't support Pexp_newtype"
  | Pexp_pack _                                   -> failwith "Matchers don't support Pexp_pack"
  | Pexp_open (_, _, _)                           -> failwith "Matchers don't support Pexp_open"
and match_pat mpat pat =
  name_self add_pat pat mpat.ppat_attributes @@
  match mpat.ppat_desc with
  (* | Ppat_extension ({txt = name; _}, PStr [])   -> add_pat name pat empty_match *)
  (* | Ppat_extension ({txt = _; _}, _)            -> failwith "Why does your matcher pattern have a Ppat_extension with a payload?" *)
  | Ppat_extension ({txt = _; _}, _)            -> failwith "Matcher's aren't using Ppat_extension right now"
  | Ppat_any                                    -> (match pat.ppat_desc with Ppat_any                                                                               -> empty_match                            | _ -> raise Match_fail)
  (* | Ppat_var {txt = mstr; _}                    -> (match pat.ppat_desc with Ppat_var {txt = str; _}                     when mstr               = str              -> empty_match                            | _ -> raise Match_fail) *)
  | Ppat_var {txt = name; _}                    -> add_pat name pat empty_match
  | Ppat_alias (mpat, {txt = mstr; _})          -> (match pat.ppat_desc with Ppat_alias (pat, {txt = str; _})            when mstr               = str              -> match_pat mpat pat                     | _ -> raise Match_fail)
  | Ppat_constant mconst                        -> (match pat.ppat_desc with Ppat_constant const                         when mconst             = const            -> empty_match                            | _ -> raise Match_fail)
  | Ppat_interval (mconst1, mconst2)            -> (match pat.ppat_desc with Ppat_interval (const1, const2)              when (mconst1, mconst2) = (const1, const2) -> empty_match                            | _ -> raise Match_fail)
  | Ppat_tuple mpats                            -> (match pat.ppat_desc with Ppat_tuple pats                                                                        -> match_pats mpats pats                  | _ -> raise Match_fail)
  | Ppat_construct ({txt = mlid; _}, Some mpat) -> (match pat.ppat_desc with Ppat_construct ({txt = lid; _}, Some pat)   when mlid               = lid              -> match_pat mpat pat                     | _ -> raise Match_fail)
  | Ppat_construct ({txt = mlid; _}, None)      -> (match pat.ppat_desc with Ppat_construct ({txt = lid; _}, None)       when mlid               = lid              -> empty_match                            | _ -> raise Match_fail)
  | Ppat_variant (mstr, Some mpat)              -> (match pat.ppat_desc with Ppat_variant (str, Some pat)                when mstr               = str              -> match_pat mpat pat                     | _ -> raise Match_fail)
  | Ppat_variant (mstr, None)                   -> (match pat.ppat_desc with Ppat_variant (str, None)                    when mstr               = str              -> match_pat mpat pat                     | _ -> raise Match_fail)
  | Ppat_record (mfields, mclosed)              -> (match pat.ppat_desc with Ppat_record (fields, closed)                when mclosed            = closed           -> match_fields match_pat mfields fields            | _ -> raise Match_fail)
  | Ppat_array mpats                            -> (match pat.ppat_desc with Ppat_array pats                                                                        -> match_pats mpats pats                  | _ -> raise Match_fail)
  | Ppat_or (mpat1, mpat2)                      -> (match pat.ppat_desc with Ppat_or (pat1, pat2)                                                                   -> match_pats [mpat1; mpat2] [pat1; pat2] | _ -> raise Match_fail)
  | Ppat_lazy mpat                              -> (match pat.ppat_desc with Ppat_lazy pat                                                                          -> match_pat mpat pat                     | _ -> raise Match_fail)
  | Ppat_exception mpat                         -> (match pat.ppat_desc with Ppat_exception pat                                                                     -> match_pat mpat pat                     | _ -> raise Match_fail)
  | Ppat_constraint _                           -> failwith "Matchers don't support Ppat_constraint"
  | Ppat_type _                                 -> failwith "Matchers don't support Ppat_type"
  | Ppat_unpack _                               -> failwith "Matchers don't support Ppat_unpack"
  | Ppat_open (_, _)                            -> failwith "Matchers don't support Ppat_open"
and match_vb mvb vb =
  name_self add_vb vb mvb.pvb_attributes @@
  let pat_match = match_pat  mvb.pvb_pat  vb.pvb_pat in
  let exp_match = match_exp_ mvb.pvb_expr vb.pvb_expr in
  merge_matches pat_match exp_match
and match_exps mexps exps = match_all match_exp_ mexps exps
and match_pats mpats pats = match_all match_pat mpats pats
and match_vbs mvbs vbs    = match_all match_vb mvbs vbs


let string_of_match m =
  (* Many OCaml functions print imperatively to a formatter. Make them return a string instead. *)
  (* Following https://github.com/ocaml/ocaml/blob/4.11/parsing/pprintast.ml string_of_expression *)
  let formatter_to_stringifier formatter =
    fun x ->
      ignore (Format.flush_str_formatter ());
      formatter Format.str_formatter x;
      Format.flush_str_formatter () in
  let string_of_pat   = formatter_to_stringifier Pprintast.pattern in
  let string_of_vb vb = string_of_pat vb.pvb_pat ^ " = " ^ Pprintast.string_of_expression vb.pvb_expr in
    "{ exps         = [" ^ String.concat ", " (List.map (fun (name, e)  -> name ^ "↦" ^ Pprintast.string_of_expression e)                  (SMap.bindings m.exps))         ^ "]\n"
  ^ "; pats         = [" ^ String.concat ", " (List.map (fun (name, p)  -> name ^ "↦" ^ string_of_pat p)                                   (SMap.bindings m.pats))         ^ "]\n"
  ^ "; vbs          = [" ^ String.concat ", " (List.map (fun (name, vb) -> name ^ "↦" ^ string_of_vb vb)                                   (SMap.bindings m.vbs))          ^ "]\n"
  ^ "; struct_items = [" ^ String.concat ", " (List.map (fun (name, si) -> name ^ "↦" ^ formatter_to_stringifier Pprintast.structure [si]) (SMap.bindings m.struct_items)) ^ "]\n"
  ^ "}"

let all_matches matcher_str struct_items =
  let matches = ref [] in
  let mexp = Parse.expression (Lexing.from_string matcher_str) in
  (* Printast.expression 0 Format.std_formatter mexp; *)
  (* print_endline @@ Pprintast.string_of_expression mexp; *)
  let def_iter = Ast_iterator.default_iterator in
  let iter_exp iter exp =
    def_iter.expr iter exp;
    try
      let match_ = match_exp_ mexp exp in
      (* print_endline (string_of_match match_); *)
      matches := match_::!matches
    with Match_fail -> ()
  in
  let iter = { def_iter with expr = iter_exp } in
  iter.structure iter struct_items;
  !matches

let subst_exp match_ name e' struct_items =
  let def_mapper = Ast_mapper.default_mapper in
  let loc = (SMap.find name match_.exps).pexp_loc in
  let map_exp mapper e =
    let e_deeper = def_mapper.Ast_mapper.expr mapper e in
    if e_deeper.pexp_loc = loc then e' else e_deeper in
  let mapper = { def_mapper with expr = map_exp } in
  mapper.structure mapper struct_items

let fill_subbed e' replacements =
  let def_mapper = Ast_mapper.default_mapper in
  let map_exp mapper e =
    let e_deeper = def_mapper.Ast_mapper.expr mapper e in
    (* let e_deeper = match e_deeper.pexp_desc with Pexp_extension ({txt = name; _}, PStr []) -> SMap.find name replacements.exps | _ -> e_deeper in *)
    let e_deeper = match e_deeper.pexp_desc with Pexp_ident {txt = Lident name; _} -> SMap.find name replacements.exps | _ -> e_deeper in
    if List.length e.pexp_attributes >= 1 then
      let ({Location.txt = name; _}, _) = List.hd e.pexp_attributes in
      let loc' = (SMap.find name replacements.exps).pexp_loc in
      { e_deeper with pexp_loc = loc'; pexp_attributes = [] }
    else
      e_deeper in
  let map_pat mapper p =
    let p_deeper = def_mapper.Ast_mapper.pat mapper p in
    (* let p_deeper = match p_deeper.ppat_desc with Ppat_extension ({txt = name; _}, PStr []) -> SMap.find name replacements.pats | _ -> p_deeper in *)
    let p_deeper = match p_deeper.ppat_desc with Ppat_var {txt = name; _} -> SMap.find name replacements.pats | _ -> p_deeper in
    if List.length p.ppat_attributes >= 1 then
      let ({Location.txt = name; _}, _) = List.hd p.ppat_attributes in
      let loc' = (SMap.find name replacements.pats).ppat_loc in
      { p_deeper with ppat_loc = loc'; ppat_attributes = [] }
    else
      p_deeper in
  let map_vb mapper vb =
    let vb_deeper = def_mapper.Ast_mapper.value_binding mapper vb in
    if List.length vb.pvb_attributes >= 1 then
      let ({Location.txt = name; _}, _) = List.hd vb.pvb_attributes in
      let loc' = (SMap.find name replacements.vbs).pvb_loc in
      { vb_deeper with pvb_loc = loc'; pvb_attributes = [] }
    else
      vb_deeper in
  let map_si mapper si =
    let si_deeper = def_mapper.Ast_mapper.structure_item mapper si in
    let si_deeper = match si_deeper.pstr_desc with Pstr_extension (({txt = name; _}, PStr []), _) -> SMap.find name replacements.struct_items | _ -> si_deeper in
    (* structure_items don't have attributes as of OCaml 4.07.1. There's a separate PStr_attribute struct item... :/ *)
    si_deeper in
  let mapper = { def_mapper with expr = map_exp; pat = map_pat; value_binding = map_vb; structure_item = map_si } in
  mapper.expr mapper e'

let rewrites matcher_str f struct_items =
  let mexp = Parse.expression (Lexing.from_string matcher_str) in
  let def_mapper = Ast_mapper.default_mapper in
  let map_exp mapper e =
    let e_deeper = def_mapper.Ast_mapper.expr mapper e in
    try
      let match_ = match_exp_ mexp e_deeper in
      print_endline (string_of_match match_);
      f match_
    with Match_fail -> e_deeper
  in
  let mapper = { def_mapper with expr = map_exp } in
  mapper.structure mapper struct_items


(* let main () =
  let matcher_str = "
     let[@vb1] y = e1 in
    (let[@vb2] x = e in e2)[@body1]" in
  let subbed_str = "
    (let[@vb2] x = e in
    (let[@vb1] y = e1 in e2)[@root])[@body1]" in
  let parsed = Camlboot_interpreter.Interp.parse "matchee" in
  (* Printast.structure 0 Format.std_formatter parsed; *)
  (* print_endline @@ Pprintast.string_of_structure parsed; *)
  let e' = Parse.expression (Lexing.from_string subbed_str) in
  let rewrite match_ =

    fill_subbed e' match_
  in
  rewrites matcher_str rewrite parsed
  |> Pprintast.string_of_structure |> print_endline
  (* all_matches matcher_str parsed
  |> List.iter (fun match_ ->
    parsed
    |> subst_exp match_ "root" e'
  ) *)
;;

main () *)
