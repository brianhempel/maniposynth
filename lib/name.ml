open Shared.Ast
open Shared.Util

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

let from_type typ =
  (Shared.Formatter_to_stringifier.f Printtyp.type_expr) typ
  |> String.map (fun c -> if Char.is_alphanum c then c else ' ')
  |> String.trim
  |> String.map (fun c -> if Char.is_alphanum c then c else '_')

let rec from_val ?(type_env = Typing.initial_env) v =
  let open Camlboot_interpreter.Data in
  let recurse = from_val ~type_env in
  match v.v_ with
  | Bomb | Hole _                 -> "var"
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
    begin try from_type (Env.lookup_constructor (Longident.Lident ctor_name) type_env).cstr_res
    with _ -> "var" end
  | Prim _                        -> "var"
  | Fexpr _                       -> "var"
  | ModVal _                      -> "var"
  | InChannel _                   -> "var"
  | OutChannel _                  -> "var"
  | Record fields                 ->
    begin match SMap.choose_opt fields with
    | Some (label, _) ->
      begin try from_type (Env.lookup_label (Longident.Lident label) type_env).lbl_res
      with _ -> "record" end
    | _ -> "record"
    end
  | Lz _                          -> "var"
  | Array _                       -> "array"
  | Fun_with_extra_args (_, _, _) -> "var"
  | Object _                      -> "var"
  | ExCall _                      -> "var"
  | ExDontCare                    -> "var"


let gen_ ~avoid ~base_name =
  let n     = ref 2 in
  let name  = ref base_name in
  while List.mem !name avoid || SSet.mem !name pervasives_names  do
    name := base_name ^ string_of_int !n;
    incr n
  done;
  !name

let gen ?(avoid = []) ?(base_name = "var") prog =
  let avoid = avoid @ StructItems.deep_names prog in
  gen_ ~avoid ~base_name

let gen_from_exp ?(avoid = []) ?type_env exp prog =
  let type_env =
    match type_env with
    | Some type_env -> type_env
    | None          -> Typing.typedtree_sig_env_of_parsed prog "unknown.ml" |> Tup3.thd
  in
  Type.of_exp_opt ~type_env exp
  |>& from_type
  |>& (fun base_name -> gen ~avoid ~base_name prog)
  ||& gen ~avoid prog
