open Shared.Ast
open Shared.Util

(*

New VBs are inserted as "unnamedN = exp" and then a better name is chosen as a separate step.
The reason for doing so is to because programs simplifications (particularly, static match flattening) produce simpler
exps which results in simpler names derived from them.
The name_unnameds function is in Bindings. (Dependency cycle otherwise.)

The the gen functions do support choosing a name immediately if you need to, which is the case if not inserting a VB.

*)

let pervasives_names =
  Env.fold_values         (fun name _ _              list -> name      :: list) None Typing.initial_env []
  @ Env.fold_constructors (fun {Types.cstr_name;  _} list -> cstr_name :: list) None Typing.initial_env []
  |> SSet.of_list

(* https://ocaml.org/releases/4.07/htmlman/names.html *)
(* https://ocaml.org/releases/4.07/htmlman/lex.html#infix-symbol *)
let infix_names = SSet.of_list ["*"; "+"; "-"; "-."; "="; "!="; "<"; ">"; "or"; "||"; "&"; "&&"; ":="; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
let infix_init_chars = CharSet.of_list ['='; '<'; '>'; '@'; '^'; '|'; '&'; '+'; '-'; '*'; '/'; '$'; '%']
let is_infix name =
  SSet.mem name infix_names ||
  (String.length name >= 1 && CharSet.mem name.[0] infix_init_chars)

let default_base_name = "unnamed"

let junk_to_name_parts =
     String.replace "->" "to"
  %> String.map (fun c -> if Char.is_letter c then c else ' ')
  %> String.trim
  %> String.uncapitalize_ascii
  %> String.split_on_whitespace

let junk_to_name = junk_to_name_parts %> List.prefix 2 %> String.concat "_"

let base_name_from_type typ =
  (Shared.Formatter_to_stringifier.f Printtyp.type_expr) typ
  |> junk_to_name

let rec base_name_from_val ?(type_env = Typing.initial_env) v =
  let open Camlboot_interpreter.Data in
  let recurse = base_name_from_val ~type_env in
  match v.v_ with
  | Bomb | Hole _                 -> default_base_name
  | Int _                         -> "int"
  | Int32 _                       -> "int32"
  | Int64 _                       -> "int64"
  | Nativeint _                   -> "nativeint"
  | Fun _                         -> "func"
  | Function _                    -> "func"
  | String _                      -> "str"
  | Float _                       -> "float"
  | Tuple vs                      -> String.concat "_" (vs |>@ recurse)
  | Constructor (ctor_name, _, _) ->
    begin try base_name_from_type (Env.lookup_constructor (Longident.Lident ctor_name) type_env).cstr_res
    with _ -> default_base_name end
  | Prim _                        -> default_base_name
  | Fexpr _                       -> default_base_name
  | ModVal _                      -> default_base_name
  | InChannel _                   -> default_base_name
  | OutChannel _                  -> default_base_name
  | Record fields                 ->
    begin match SMap.choose_opt fields with
    | Some (label, _) ->
      begin try base_name_from_type (Env.lookup_label (Longident.Lident label) type_env).lbl_res
      with _ -> "record" end
    | _ -> "record"
    end
  | Lz _                          -> default_base_name
  | Array _                       -> "array"
  | Fun_with_extra_args (_, _, _) -> default_base_name
  | Object _                      -> default_base_name
  | ExCall _                      -> default_base_name
  | ExDontCare                    -> default_base_name


let gen_ ~avoid ~base_name =
  let n     = ref 2 in
  let name  = ref base_name in
  while List.mem !name avoid || SSet.mem !name pervasives_names  do
    name := base_name ^ string_of_int !n;
    incr n
  done;
  !name

let gen ?(avoid = []) ?(base_name = default_base_name) prog =
  let avoid = avoid @ StructItems.deep_names prog in
  gen_ ~avoid ~base_name

(* tries make exp a name if valid, otherwise from type *)
let gen_from_exp ?(avoid = []) ?type_env exp prog =
  let code          = Exp.to_string exp in
  let name_from_exp = junk_to_name code in
  let avoid         = String.split_on_whitespace code @ avoid in
  let base_name_opt =
    if String.length name_from_exp >= 1 && List.length (Scope.free_unqualified_names exp) >= 1 then
      Some name_from_exp
    else
      let type_env =
        match type_env with
        | Some type_env -> type_env
        | None          -> Typing.typedtree_sig_env_of_parsed_with_error_recovery prog "unknown.ml" |> Tup3.thd
      in
      Type.of_exp_opt ~type_env exp
      |>& base_name_from_type
  in
  gen ~avoid ?base_name:base_name_opt prog


(* Currently, unnamedN is only inserted on the LHS of single pat VBs. *)
(* Precondition: VB LOCS MUST BE FRESH! *)
let name_unnameds ?type_env prog =
  let try_rename vb prog =
    match vb |> Vb.pat |> Pat.single_name with
    | Some name when String.starts_with default_base_name name ->
      Scope.rename_pat_by_loc (Pat.loc (Vb.pat vb)) (gen_from_exp ?type_env (Vb.exp vb) prog) prog
    | _ ->
      prog
  in
  List.fold_right try_rename (Vb.all prog) prog
