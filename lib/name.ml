open Shared.Ast
open Shared.Util

module SSet = Set.Make(String)

let pervasives_names =
  let initial_env = Compmisc.initial_env () in
  Env.fold_values         (fun name _ _              list -> name      :: list) None initial_env []
  @ Env.fold_constructors (fun {Types.cstr_name;  _} list -> cstr_name :: list) None initial_env []
  |> SSet.of_list


let from_type typ =
  (Shared.Formatter_to_stringifier.f Printtyp.type_expr) typ
  |> String.map (fun c -> if Char.is_alphanum c then c else ' ')
  |> String.trim
  |> String.map (fun c -> if Char.is_alphanum c then c else '_')

let rec from_val ?(type_env = Typing.inital_env) v =
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

let gen ?(avoid = []) ?(base_name = "var") prog =
  let avoid = avoid @ StructItems.names prog in
  let n     = ref 2 in
  let name  = ref base_name in
  while List.mem !name avoid || SSet.mem !name pervasives_names  do
    name := base_name ^ string_of_int !n;
    incr n
  done;
  !name

