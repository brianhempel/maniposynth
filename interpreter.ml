open Base
open Stdio

let warn loc msg =
  Location.prerr_alert loc { kind = "Interpreter"; message = msg; def = loc; use = loc }

let lazy_or opt ~f =
  match opt with
  | Some _ -> opt
  | None   -> f ()

let is_finished pid =
  match Unix.waitpid [Unix.WNOHANG] pid with
  | (0, _) -> false
  | _      -> true

(* Runs command and returns its std out as a string *)
let command ?(verbose = false) cmd =
  if verbose then
    print_endline cmd;
  let chunk_size = 1000 in
  let chan       = Unix.open_process_in cmd in
  let pid        = Unix.process_in_pid chan in
  let str        = ref "" in
  let bytes_buf  = Bytes.create chunk_size in
  let rec read_until_process_exit () =
    let len_read = In_channel.input chan ~buf:bytes_buf ~pos:0 ~len:chunk_size in
    if len_read = 0 && is_finished pid then
      ()
    else if len_read = 0 then
      read_until_process_exit ()
    else begin
      str := !str ^ Stdlib.Bytes.sub_string bytes_buf 0 len_read;
      read_until_process_exit ()
    end
  in
  read_until_process_exit ();
  In_channel.close chan;
  if verbose then
    print_string !str;
  !str;;

module TT = Typedtree

type value_env = (Ident.t * value) list
and value
  = Fun of
      { value_env_ref : value_env ref
      ; arg_label     : Asttypes.arg_label
      ; param         : Ident.t
      ; cases         : TT.value TT.case list
      ; partial       : TT.partial (* type partial = Partial | Total *)
      }
  | Int     of int
  | Float   of float
  | Char    of char
  | String  of string
  | Tuple   of value list
  | Ctor    of string * value list
  | Variant of string * value option (* polymorphic variant, e.g. `JsonStr str *)
  | Record  of field list
  | Array   of value list
  | Bomb    of Warnings.loc * string (* if used, crash and print the error string *)
and field = string * value

(* cons_env new_bindings existing_bindings = *)

(*
LHS of a let-rec is always a single variable. Yay!

Besides functions, what's allowed on the RHS of a let-rec is a bit tricky. See:
https://caml.inria.fr/pub/docs/manual-ocaml/letrecvalues.html#s%3Aletrecvalues

We will allow items that do not use any recursive variables, which will
allow constants (as OCaml does).
*)
(* longidents A.x not supported *)
(* constructor uses and polymorphic variants are not considered "vars" *)
let rec free_vars (texp : TT.expression) : Ident.Set.t =
  let union_all = List.fold ~init:Ident.Set.empty ~f:Ident.Set.union in
  let arg_free_vars = function
    | (Asttypes.Nolabel, None)       -> failwith "what the heck: unlabeled application arg with no arg expression?!"
    | (Asttypes.Labelled name, None)
    | (Asttypes.Optional name, None) -> Ident.Set.singleton (Ident.create_local name)
    | (_, Some arg_exp)              -> free_vars arg_exp
  in
  let fields_free_vars fields =
    let field_free_vars = function
      | (_, TT.Kept _)              -> Ident.Set.empty
      | (_, TT.Overridden (_, exp)) -> free_vars exp
    in
    fields
    |> Array.fold ~init:Ident.Set.empty ~f:(fun set field -> Ident.Set.union set (field_free_vars field))
  in
  match texp.exp_desc with
  | TT.Texp_ident (_, {txt = Longident.Lident name; _}, _) -> Ident.Set.singleton (Ident.create_local name)
  | TT.Texp_ident (_, {txt = _                    ; _}, _) -> failwith "free_vars Texp_ident can't hand complex longidents; Ocaml's lambda rep seems to ignore the path and only could the final ident string as free, but that doesn't make sense"
  | TT.Texp_constant _                                     -> Ident.Set.empty
  | TT.Texp_let (Nonrecursive, vbs, body)                  -> Ident.Set.union (vbs_free_vars vbs) @@ remove_idents (TT.let_bound_idents vbs) (free_vars body)
  | TT.Texp_let (Recursive,    vbs, body)                  -> remove_idents (TT.let_bound_idents vbs) @@ Ident.Set.union (vbs_free_vars vbs) (free_vars body)
  | TT.Texp_function { param; cases; _ }                   -> Ident.Set.remove param @@ cases_free_vars cases
  | TT.Texp_apply (f, args)                                -> union_all @@ free_vars f :: List.map ~f:arg_free_vars args
  | TT.Texp_match (scrutinee, cases, _)                    -> Ident.Set.union (free_vars scrutinee) (computation_cases_free_vars cases)
  | TT.Texp_try (body, cases)                              -> Ident.Set.union (free_vars body) (cases_free_vars cases)
  | TT.Texp_tuple exps                                     -> union_all @@ List.map ~f:free_vars exps
  | TT.Texp_construct (_lid_loced, _, exps)                -> union_all @@ List.map ~f:free_vars exps
  | TT.Texp_variant (_, Some exp)                          -> free_vars exp
  | TT.Texp_variant (_, None)                              -> Ident.Set.empty
  | TT.Texp_record { fields; extended_expression; _ }      -> Ident.Set.union (fields_free_vars fields) (texp_opt_free_vars extended_expression)
  | TT.Texp_field (exp, _, _)                              -> free_vars exp
  | TT.Texp_setfield (record_exp, _, _, field_exp)         -> Ident.Set.union (free_vars record_exp) (free_vars field_exp)
  | TT.Texp_array exps                                     -> union_all @@ List.map ~f:free_vars exps
  | TT.Texp_ifthenelse (cond_exp, then_exp, else_exp_opt)  -> union_all @@ List.map ~f:free_vars (cond_exp :: then_exp :: Option.to_list else_exp_opt)
  | TT.Texp_sequence (lexp, rexp)                          -> Ident.Set.union (free_vars lexp) (free_vars rexp)
  | TT.Texp_while (cond_exp, body)                         -> Ident.Set.union (free_vars cond_exp) (free_vars body)
  | TT.Texp_for (name, _, lo, hi, _, body)                 -> union_all [free_vars lo; free_vars hi; Ident.Set.remove name @@ free_vars body]
  | TT.Texp_send (_, _, _)                                 -> failwith "OO not supported"
  | TT.Texp_new (_, _, _)                                  -> failwith "OO not supported"
  | TT.Texp_instvar (_, _, _)                              -> failwith "OO not supported"
  | TT.Texp_setinstvar (_, _, _, _)                        -> failwith "OO not supported"
  | TT.Texp_override (_, _)                                -> failwith "OO not supported"
  | TT.Texp_letmodule (_, _, _, _, body)                   -> free_vars body (* ignoring longidents for now *)
  | TT.Texp_letexception (_, body)                         -> free_vars body (* ignoring constructor names *)
  | TT.Texp_assert exp                                     -> free_vars exp
  | TT.Texp_lazy exp                                       -> free_vars exp
  | TT.Texp_object (_, _)                                  -> failwith "OO not supported"
  | TT.Texp_pack _                                         -> failwith "modules not supported"
  | TT.Texp_letop _                                        -> failwith "fancypants bind syntax not supported"
  | TT.Texp_unreachable                                    -> Ident.Set.empty
  | TT.Texp_extension_constructor (_, _)                   -> failwith "extensions not supported"
  | TT.Texp_open (open_infos, body)                        -> remove_idents (List.concat_map ~f:sig_val_names open_infos.open_bound_items) (free_vars body)
and sig_val_names tsig_item =
  match tsig_item with
  | Types.Sig_value (ident, _, Exported) -> [ident]
  | _                                    -> []
and texp_opt_free_vars (texp_opt : TT.expression option) =
  Option.map texp_opt ~f:free_vars |> Option.value ~default:Ident.Set.empty
and remove_idents ident_list set =
  ident_list
  |> List.fold ~init:set ~f:(fun set ident -> Ident.Set.remove ident set)
and vbs_free_vars (vbs : TT.value_binding list) : Ident.Set.t =
  vbs
  |> List.fold ~init:Ident.Set.empty ~f:(fun set vb -> Ident.Set.union set @@ free_vars vb.TT.vb_expr)
and cases_free_vars (cases : TT.value TT.case list) : Ident.Set.t =
  let case_free_vars { TT.c_lhs; c_guard; c_rhs } =
    let guard_idents = texp_opt_free_vars c_guard in
    remove_idents (TT.pat_bound_idents c_lhs) (Ident.Set.union guard_idents @@ free_vars c_rhs)
  in
  cases
  |> List.fold ~init:Ident.Set.empty ~f:(fun set case -> Ident.Set.union set @@ case_free_vars case)
and computation_cases_free_vars (cases : TT.computation TT.case list) : Ident.Set.t =
  (* Exactly the same as the above. HM fail. *)
  let case_free_vars { TT.c_lhs; c_guard; c_rhs } =
    let guard_idents = Option.map c_guard ~f:free_vars |> Option.value ~default:Ident.Set.empty in
    remove_idents (TT.pat_bound_idents c_lhs) (Ident.Set.union guard_idents @@ free_vars c_rhs)
  in
  cases
  |> List.fold ~init:Ident.Set.empty ~f:(fun set case -> Ident.Set.union set @@ case_free_vars case)

(* These are the cases allowed by Translcore.transl_let for LHS of let recs *)
let single_ident_of_pat_opt pat =
  match pat.TT.pat_desc with
  | TT.Tpat_var (ident, _)                                -> Some ident
  | TT.Tpat_alias ({pat_desc = TT.Tpat_any; _}, ident, _) -> Some ident
  | _                                                     -> None


(* let parse str = Lexing.from_string str |> Parse.expression *)
(* Translcore.transl_exp ~scopes:[] @@ Typecore.type_exp Env.empty (parse "5.0");; *)

let rec pattern_match (tpat : TT.pattern) (value : value) : value_env option =
  let match_constant (constant : Asttypes.constant) (value : value) =
    let open Asttypes in
    match (constant, value) with
    | (Const_int pint            , Int vint)     -> Int.equal pint vint
    | (Const_char pchar          , Char vchar)   -> Char.equal pchar vchar
    | (Const_string (pstr, _, _) , String vstr)  -> String.equal pstr vstr
    | (Const_float pfloat_str    , Float vfloat) -> Float.equal (Float.of_string pfloat_str) vfloat
    | (Const_int32 _             , _)            -> failwith "int32 patterns not supported"
    | (Const_int64 _             , _)            -> failwith "int64 patterns not supported"
    | (Const_nativeint _         , _)            -> failwith "nativeint patterns not supported"
    | _                                          -> false
  in
  let match_list pats values =
    match List.map2 pats values ~f:pattern_match with
    | Ok env_opts -> env_opts |> Option.all |> Option.map ~f:List.concat
    | _           -> None (* unequal lengths *)
  in
  let match_tuple pats value =
    match value with
    | Tuple values -> match_list pats values
    | _            -> None
  in
  let match_ctor name arg_pats value =
    match value with
    | Ctor (ctor_name, values) when String.equal name ctor_name -> match_list arg_pats values
    | _                                                         -> None
  in
  let match_variant name arg_pat_opt value =
    match value with
    | Variant (variant_name, arg_opt) when String.equal name variant_name -> match_list (Option.to_list arg_pat_opt) (Option.to_list arg_opt)
    | _                                                                   -> None
  in
  let match_record pfields value =
    match value with
    | Record vfields ->
      pfields
      |> List.map ~f:begin function
        | ({ Location.txt = Longident.Lident field_name; _ }, _, pat) -> begin
            match List.Assoc.find vfields ~equal:String.equal field_name with
            | Some field_val -> pattern_match pat field_val
            | None           -> None
          end
        | _ -> failwith "record field longidents not supported"
      end
      |> Option.all
      |> Option.map ~f:List.concat
    | _ -> None
  in
  let match_array pats value =
    match value with
    | Array values -> match_list pats values
    | _            -> None
  in
  match tpat.pat_desc with
  | TT.Tpat_any                                                       -> Some []
  | TT.Tpat_var (ident, _)                                            -> Some [(ident, value)]
  | TT.Tpat_alias (pat', ident, _)                                    -> pattern_match pat' value |> Option.map ~f:(List.cons (ident, value))
  | TT.Tpat_constant constant                                         -> if match_constant constant value then Some [] else None
  | TT.Tpat_tuple pats                                                -> match_tuple pats value
  | TT.Tpat_construct ({txt = Longident.Lident name; _}, _, arg_pats) -> match_ctor name arg_pats value
  | TT.Tpat_construct ({txt = _;                     _}, _, _)        -> failwith "longidents not supported in pattern matches"
  | TT.Tpat_variant (name, arg_pat_opt, _)                            -> match_variant name arg_pat_opt value
  | TT.Tpat_record (fields, _)                                        -> match_record fields value
  | TT.Tpat_array pats                                                -> match_array pats value
  | TT.Tpat_lazy _                                                    -> failwith "lazy patterns not supported"
  | TT.Tpat_or (pat1, pat2, None)                                     -> lazy_or (pattern_match pat1 value) ~f:(fun () -> pattern_match pat2 value)
  | TT.Tpat_or (_, _, Some _)                                         -> failwith "or pats with the row thing are not supported"

let rec eval (val_env : value_env) (texp : TT.expression) : value =
  let env_lookup val_env ident = List.Assoc.find val_env ~equal:Ident.equal ident in
  let eval_constant =
    let open Asttypes in
    function
    | Const_int int_           -> Int int_
    | Const_char char_         -> Char char_
    | Const_string (str, _, _) -> String str
    | Const_float float_str    -> Float (Float.of_string float_str)
    | Const_int32 _            -> failwith "eval Const_int32 not supported"
    | Const_int64 _            -> failwith "eval Const_int64 not supported"
    | Const_nativeint _        -> failwith "eval nativeint not supported"
  in
  let apply val_env f_val arg_exps =
    (??)
  in
  match texp.exp_desc with
  | TT.Texp_ident (_, {txt = Longident.Lident name; loc}, _) -> (match env_lookup val_env (Ident.create_local name) with Some value -> value | None -> Bomb (loc, "Variable not found: " ^ name))
  | TT.Texp_ident (_, {txt = _                    ; _  }, _) -> failwith "eval Texp_ident can't hand complex longidents"
  | TT.Texp_constant ast_const                               -> eval_constant ast_const
  | TT.Texp_let (Nonrecursive, vbs, body)                    -> eval (eval_value_bindings val_env vbs) body
  | TT.Texp_let (Recursive,    vbs, body)                    -> eval (eval_mutually_recursive_value_bindings val_env vbs) body
  | TT.Texp_function { arg_label; param; cases; partial }    -> Fun { value_env_ref = ref val_env; arg_label = arg_label; param = param; cases = cases; partial = partial }
  | TT.Texp_apply (f, arg_exps)                              -> apply val_env (eval f) arg_exps
  | TT.Texp_match (scrutinee, cases, _)                      -> (??)
  | TT.Texp_try (body, cases)                                -> (??)
  | TT.Texp_tuple exps                                       -> (??)
  | TT.Texp_construct (_lid_loced, _, exps)                  -> (??)
  | TT.Texp_variant (_, Some exp)                            -> (??)
  | TT.Texp_variant (_, None)                                -> (??)
  | TT.Texp_record { fields; extended_expression; _ }        -> (??)
  | TT.Texp_field (exp, _, _)                                -> (??)
  | TT.Texp_setfield (record_exp, _, _, field_exp)           -> (??)
  | TT.Texp_array exps                                       -> (??)
  | TT.Texp_ifthenelse (cond_exp, then_exp, else_exp_opt)    -> (??)
  | TT.Texp_sequence (lexp, rexp)                            -> (??)
  | TT.Texp_while (cond_exp, body)                           -> (??)
  | TT.Texp_for (name, _, lo, hi, _, body)                   -> (??)
  | TT.Texp_send (_, _, _)                                   -> failwith "OO not supported"
  | TT.Texp_new (_, _, _)                                    -> failwith "OO not supported"
  | TT.Texp_instvar (_, _, _)                                -> failwith "OO not supported"
  | TT.Texp_setinstvar (_, _, _, _)                          -> failwith "OO not supported"
  | TT.Texp_override (_, _)                                  -> failwith "OO not supported"
  | TT.Texp_letmodule (_, _, _, _, body)                     -> (??)
  | TT.Texp_letexception (_, body)                           -> (??)
  | TT.Texp_assert exp                                       -> (??)
  | TT.Texp_lazy exp                                         -> (??)
  | TT.Texp_object (_, _)                                    -> failwith "OO not supported"
  | TT.Texp_pack _                                           -> failwith "modules not supported"
  | TT.Texp_letop _                                          -> failwith "fancypants bind syntax not supported"
  | TT.Texp_unreachable                                      -> (??)
  | TT.Texp_extension_constructor (_, _)                     -> failwith "extensions not supported"
  | TT.Texp_open (open_infos, body)                          -> (??)

and eval_mutually_recursive_value_bindings val_env (vbs : TT.value_binding list) : value_env =
  let rec_ident_set = Ident.Set.of_list @@ TT.let_bound_idents vbs in
  let new_env_ref = ref val_env in
  vbs
  |> List.iter ~f:(fun { TT.vb_pat; vb_expr; vb_loc; _ } ->
    match single_ident_of_pat_opt vb_pat with
    | Some ident -> begin
        let value = if Ident.Set.disjoint rec_ident_set (free_vars vb_expr) then eval val_env vb_expr else Bomb (vb_expr.exp_loc, "unhandlable let rec RHS. only constants and functions are supported") in
        let value' =
          match value with
          | Fun stuff -> Fun { stuff with value_env_ref = new_env_ref }
          | _         -> value
        in
        new_env_ref := (ident, value') :: !new_env_ref
      end
    | None -> warn vb_loc "let rec RHS does not have only a single bare var"
  );
  !new_env_ref

and eval_value_bindings val_env (vbs : TT.value_binding list) : value_env =
  match vbs with
  | [] -> val_env
  | { TT.vb_pat; vb_expr; _ } :: rest ->
    let value = eval val_env vb_expr in
    let val_env' = begin
      match pattern_match vb_pat value with
      | Some bindings -> bindings @ val_env
      | None          -> failwith "pattern match failure in let"
    end in
    eval_value_bindings val_env' rest

let eval_str_item val_env (structure_item : TT.structure_item) =
  let do_nothing = val_env in
  match structure_item.str_desc with
  | TT.Tstr_eval (_, _)               -> failwith "unhandled Tstr_eval"
  | TT.Tstr_value (Nonrecursive, vbs) -> eval_value_bindings val_env vbs
  | TT.Tstr_value (Recursive, vbs)    -> eval_mutually_recursive_value_bindings val_env vbs
  | TT.Tstr_primitive _               -> failwith "unhandled Tstr_primitive"
  | TT.Tstr_type (Nonrecursive, _)    -> failwith "unhandled Tstr_type"
  | TT.Tstr_type (Recursive, _)       -> do_nothing
  | TT.Tstr_typext _                  -> failwith "unhandled Tstr_typext"
  | TT.Tstr_exception _               -> failwith "unhandled Tstr_exception"
  | TT.Tstr_module _                  -> failwith "unhandled Tstr_module"
  | TT.Tstr_recmodule _               -> failwith "unhandled Tstr_recmodule"
  | TT.Tstr_modtype _                 -> failwith "unhandled Tstr_modtype"
  | TT.Tstr_open _                    -> failwith "unhandled Tstr_open"
  | TT.Tstr_class _                   -> failwith "unhandled Tstr_class"
  | TT.Tstr_class_type _              -> failwith "unhandled Tstr_class_type"
  | TT.Tstr_include _                 -> failwith "unhandled Tstr_include"
  | TT.Tstr_attribute _               -> failwith "unhandled Tstr_attribute"

let rec eval_str_items val_env (structure_items : TT.structure_item list) =
  match structure_items with
  | [] -> ()
  | str_item::rest ->
    let val_env' = eval_str_item val_env str_item in
    eval_str_items val_env' rest

let main () =
  (* print_endline "hi"; *)
  ignore @@ command "ocamlc -stop-after typing -bin-annot simple.ml";
  let open Cmt_format in
  let cmt = read_cmt "simple.cmt" in
  match cmt.cmt_annots with
  | Implementation typedtree -> eval_str_items [] typedtree.str_items
      (* https://discuss.ocaml.org/t/getting-the-environment-from-the-ast-in-cmt/4287/2 *)
      (* and  https://github.com/ocaml/ocaml/blob/4.11/tools/read_cmt.ml *)
      (* Envaux.reset_cache (); *)
      (* List.iter Load_path.add_dir (List.rev cmt.cmt_loadpath); *)
      (* (Envaux.env_of_only_summary structure.str_final_env, structure) *)
      (* (Envaux.env_of_only_summary (List_utils.last structure.str_items).str_env, structure) *)
  | Partial_implementation _ -> failwith "Cmt_format.Partial_implementation"
  | Packed (_, _)            -> failwith "Cmt_format.Packed"
  | Interface _              -> failwith "Cmt_format.Interface"
  | Partial_interface _      -> failwith "Cmt_format.Partial_interface"
;;

main ()
