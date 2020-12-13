
let warn loc msg =
  Location.prerr_alert loc { kind = "Interpreter"; message = msg; def = loc; use = loc }

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
    let len_read = input chan bytes_buf 0 chunk_size in
    if len_read = 0 && is_finished pid then
      ()
    else if len_read = 0 then
      read_until_process_exit ()
    else begin
      str := !str ^ Bytes.sub_string bytes_buf 0 len_read;
      read_until_process_exit ()
    end
  in
  read_until_process_exit ();
  close_in_noerr chan;
  if verbose then
    print_string !str;
  !str;;

module TT = Typedtree

type value_env = (Ident.t * value) list
and value
  = VFun of
      { value_env_ref : value_env ref
      ; arg_label     : Asttypes.arg_label
      ; param         : Ident.t
      ; cases         : TT.value TT.case list
      ; partial       : TT.partial (* type partial = Partial | Total *)
      }
  | Bomb of Warnings.loc * string (* if used, crash and print the error string *)

(* cons_env new_bindings existing_bindings = *)

(*
LHS of a let-rec is always a single variable. Yay!

Besides functions, what's allowed on the RHS of a let-rec is a bit tricky. See:
https://caml.inria.fr/pub/docs/manual-ocaml/letrecvalues.html#s%3Aletrecvalues

We will allow items that do not use any recursive variables, which will
allow constants (as OCaml does).
*)
let free_vars (texp : TT.expression) : Ident.Set.t =
  (* START HERE. In Typecore, see Env.add_value / Typecore.type_ident / Env.lookup_value. *)
  (match texp with
| { exp_desc; exp_loc; exp_extra; exp_type; exp_env; exp_attributes } -> (??))

(* Based on Lambda.free_variables_list *)
let union_var_sets texprs =
  List.fold_left (fun set expr -> Ident.Set.union (free_vars expr) set)
    Ident.Set.empty texprs

(* These are the cases allowed by Translcore.transl_let for LHSes of let recs *)
let single_ident_of_pat_opt pat =
  match pat.TT.pat_desc with
  | TT.Tpat_var (ident, _)                              -> Some ident
  | TT.Tpat_alias ({pat_desc=TT.Tpat_any; _}, ident, _) -> Some ident
  | _                                                   -> None

let eval _val_env texp = Bomb (texp.TT.exp_loc, "")

let eval_mutually_recursive_value_bindings val_env (vbs : TT.value_binding list) : value_env =
  let rec_ident_set = Ident.Set.of_list @@ TT.let_bound_idents vbs in
  let new_env_ref = ref val_env in
  vbs
  |> List.iter (fun { TT.vb_pat; vb_expr; vb_loc; _ } ->
    match single_ident_of_pat_opt vb_pat with
    | Some ident -> begin
        let value = if Ident.Set.disjoint rec_ident_set (free_vars vb_expr) then eval val_env vb_expr else Bomb (vb_expr.exp_loc, "unhandlable let rec RHS. only constants and functions are supported") in
        let value' =
          match value with
          | VFun stuff -> VFun { stuff with value_env_ref = new_env_ref }
          | _          -> value
        in
        new_env_ref := (ident, value') :: !new_env_ref
      end
    | None -> warn vb_loc "let rec RHS does not have a single var"
  );
  !new_env_ref

let eval_str_item val_env (structure_item : TT.structure_item) =
  let do_nothing = val_env in
  match structure_item.str_desc with
  | TT.Tstr_eval (_, _)                -> failwith "unhandled Tstr_eval"
  | TT.Tstr_value (Nonrecursive, _vbs) -> failwith "unhandled Tstr_value"
  | TT.Tstr_value (Recursive, vbs)     -> eval_mutually_recursive_value_bindings val_env vbs
  | TT.Tstr_primitive _                -> failwith "unhandled Tstr_primitive"
  | TT.Tstr_type (Nonrecursive, _)     -> failwith "unhandled Tstr_type"
  | TT.Tstr_type (Recursive, _)        -> do_nothing
  | TT.Tstr_typext _                   -> failwith "unhandled Tstr_typext"
  | TT.Tstr_exception _                -> failwith "unhandled Tstr_exception"
  | TT.Tstr_module _                   -> failwith "unhandled Tstr_module"
  | TT.Tstr_recmodule _                -> failwith "unhandled Tstr_recmodule"
  | TT.Tstr_modtype _                  -> failwith "unhandled Tstr_modtype"
  | TT.Tstr_open _                     -> failwith "unhandled Tstr_open"
  | TT.Tstr_class _                    -> failwith "unhandled Tstr_class"
  | TT.Tstr_class_type _               -> failwith "unhandled Tstr_class_type"
  | TT.Tstr_include _                  -> failwith "unhandled Tstr_include"
  | TT.Tstr_attribute _                -> failwith "unhandled Tstr_attribute"


let rec eval_str_items (structure_items : TT.structure_item list) =
  match structure_items with
  | [] -> ()
  | str_item::rest ->
    ignore (eval_str_item [] str_item);
    eval_str_items rest


let eval_structure (structure : TT.structure) =
  eval_str_items structure.str_items


let main () =
  (* print_endline "hi"; *)
  ignore @@ command "ocamlc -stop-after typing -bin-annot simple.ml";
  let open Cmt_format in
  let cmt = read_cmt "simple.cmt" in
  match cmt.cmt_annots with
  | Implementation typedtree -> eval_structure typedtree
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
