open Asttypes
open Parsetree

module SMap = Shared.Util.SMap
module SSet = Shared.Util.SSet

type frame_no = int (* execution frame numbers for tracing *)

type module_unit_id = Path of string
module UStore = Map.Make(struct
  type t = module_unit_id
  let compare (Path a) (Path b) = String.compare a b
end)

(* vtraces don't serialize reliably enough across identical runs *)
type value = { v_ : value_; vtrace : vtrace; type_opt : Types.type_expr option }
and value_ =
  | Bomb (* Evalution hit some error, e.g. a hole made it to elimination position *)
  | Hole of (env ref * frame_no * expression) (* Evalution hit a hole - allows pushing requirements into bare holes in e.g. let not_a_func_yet = (??) in assert (not_a_func_yet [] = 0) *)
  | Int of int
  | Int32 of int32
  | Int64 of int64
  | Nativeint of nativeint
  | Fun of arg_label * expression option * pattern * expression * env ref
  | Function of case list * env ref
  | String of bytes
  | Float of float
  | Tuple of value list
  | Constructor of string * int * value option
  | Prim of string * (value -> value)
  | Fexpr of fexpr
  | ModVal of mdl
  | InChannel of in_channel
  | OutChannel of out_channel
  | Record of value ref SMap.t
  | Lz of (unit -> value) ref
  | Array of value array
  | Fun_with_extra_args of value * value list * (arg_label * value) SMap.t
  | Object of object_value
  (* --- Only used in synth examples --- *)
  | ExCall of value * value (* v1 -> v2 *)
  | ExDontCare
  (* ----------------------------------- *)

and fexpr = Location.t -> (arg_label * expression) list -> expression option

and vtrace = (trace_pt * tp_type) list
and trace_pt = frame_no * Location.t
and tp_type =
  | Intro (* val introduction *)
  | Use (* var usage *)
  | Ret (* pass-through expression return (e.g. function application result) *)
  | PatMatch of value * projection list (* subvalue path within a root value *)
and projection =
  | Child of int (* 0-indexed *)
  | Field of string

and 'a env_map = (bool * 'a) SMap.t
(* the boolean tracks whether the value should be exported in the
   output environment *)

and env = {
  values : value_or_lvar env_map;
  modules : mdl env_map;
  constructors : int env_map;
  classes : class_def env_map;
  current_object : object_value option;
}

and value_or_lvar =
  | Value of value
  | Instance_variable of object_value * string

and class_def = class_expr * env ref

and mdl =
  | Unit of module_unit_id * module_unit_state ref
  | Module of mdl_val
  | Functor of string * module_expr * env

and mdl_val = {
    mod_values : value SMap.t;
    mod_modules : mdl SMap.t;
    mod_constructors : int SMap.t;
    mod_classes : class_def SMap.t;
    mod_internal_env : env
  }

and module_unit_state =
  | Not_initialized_yet
  | Initialized of mdl_val
(* OCaml calls a "compilation unit" the language object corresponding
   to a group of files of the same name with different extensions
   (foo.ml, foo.mli in source form, foo.cm* in compiled form). From
   the language those are also visible implicitly as modules (Foo),
   but they are not exactly identical to modules as well -- in what
   sort of dependencies are allowed between units, in particular.

   Instead of "compilation units" which sounds strange in an
   interpreter, we just call these "module units" or "units".

   In our value representation, some of the modules in the environment
   may in fact be units (a unit is a category of module), and
   initialized units contain module data, like a normal module.

   The -no-alias-deps flag allows an OCaml source fragment to create
   an alias to a unit that has not been evaluated yet -- allowing
   cyclic dependencies where each cycle contains a "weak" edge that is
   just a module-alias occurrence

   From an operational point of view, this corresponds to allowing
   implicit recursive definition of units, where all units can
   alias/reference each other (even units evaluated later), but a unit
   may only dereference (access the module data of) a unit evaluated
   earlier.

   To support these recursive definitions, we give backpatching
   semantics to unit definitions: all the units that are to be
   evaluated are loaded at once in the environment as (references to)
   "non initialized" units, and after each unit is evaluated to some
   module data we mutate its state in the environment, which makes
   non-aliasing uses possible for further units.
*)

and object_value = {
  env: env;
  self: pattern;
  initializers: expr_in_object list;
  named_parents: object_value SMap.t;
  variables: value ref SMap.t;
  methods: expr_in_object SMap.t;

  parent_view: string list;
  (* When evaluating a call super#foo, it would be wrong to just
     resolve the call in a parent object bound to the 'super'
     identifier in the current environment. Indeed, when then
     executing the code of super#foo, self-calls of the form self#bar
     would be resolved in the parent object 'super', instead of in the
     current object 'self', which is the intended late-binding
     semantics.

     To solve this issue, we bind 'super' not to the parent object,
     but to the *current* object "viewed as its parent 'super'"; the
     'parent_view' field stores that view (in general there may be
     several levels of super-calls nesting, so it's a list). The view
     affects how methods are resolved -- their code is looked up
     in the right parent object.
   *)
}
and source_object =
  | Current_object
  | Parent of object_value
and expr_in_object = {
  source : source_object;

  instance_variable_scope : SSet.t;
  (** The scoping of instance variables within object declarations
      makes them in the scope of only some of the expressions in methods
      and initializers; an "instance variable scope" remembers the set
      of instance variables that are in scope of a given expression). *)

  named_parents_scope : SSet.t;
  (** Similarly, it may be that only some of the 'inherit foo as x' fields
      scope over the current piece of code, so we keep a set of visible parents.

      Remark: the self-pattern is always at the beginning of a class
      or object declaration, so it is in the scope of all
      expressions. *)

  expr : expression;
}

exception InternalException of value

type assert_result =
  { env          : env
  ; lhs_exp      : expression
  ; expected_exp : expression
  ; actual       : value
  ; expected     : value
  ; passed       : bool
  }

let new_vtrace v_ = { v_ = v_; vtrace = []; type_opt = None }
let add_type_opt type_opt v = { v with type_opt = type_opt }

let unit = new_vtrace @@ Constructor ("()", 0, None)

exception BombExn

let is_true { v_; _ } =
  match v_ with
  | Constructor ("true", _, None) -> true
  | Constructor ("false", _, None) -> false
  | _ -> raise BombExn

let rec pp_print_value ff { v_; _ } =
  match v_ with
  | Bomb -> Format.fprintf ff "💣"
  | Hole _ -> Format.fprintf ff "(??)"
  | Int n -> Format.fprintf ff "%d" n
  | Int32 n -> Format.fprintf ff "%ldl" n
  | Int64 n -> Format.fprintf ff "%LdL" n
  | Nativeint n -> Format.fprintf ff "%ndn" n
  | Fexpr _ -> Format.fprintf ff "<fexpr>"
  | Fun _ -> Format.fprintf ff "<fun>"
  | Function _ -> Format.fprintf ff "<function>"
  | Prim (prim_name, _) ->  Format.fprintf ff "<prim %s>" prim_name
  | Lz _ | Fun_with_extra_args _ -> Format.fprintf ff "<function_other>"
  | String s -> Format.fprintf ff "%S" (Bytes.to_string s)
  | Float f -> Format.fprintf ff "%f" f
  | Tuple l ->
    Format.fprintf
      ff
      "(%a)"
      (Format.pp_print_list
         ~pp_sep:(fun ff () -> Format.fprintf ff ", ")
         pp_print_value)
      l
  | Constructor (c, d, None) -> Format.fprintf ff "%s#%d" c d
  | Constructor (c, d, Some v) ->
    Format.fprintf ff "%s#%d %a" c d pp_print_value v
  | ModVal _ -> Format.fprintf ff "<module>"
  | InChannel _ -> Format.fprintf ff "<in_channel>"
  | OutChannel _ -> Format.fprintf ff "<out_channel>"
  | Record r ->
    Format.fprintf ff "{";
    SMap.iter (fun k v -> Format.fprintf ff "%s = %a; " k pp_print_value !v) r;
    Format.fprintf ff "}"
  | Array a ->
    Format.fprintf
      ff
      "[|%a|]"
      (Format.pp_print_list
         ~pp_sep:(fun ff () -> Format.fprintf ff "; ")
         pp_print_value)
      (Array.to_list a)
  | Object _ -> Format.fprintf ff "<object>"
  | ExCall (v1, v2) -> Format.fprintf ff "%a -> %a" pp_print_value v1 pp_print_value v2
  | ExDontCare -> Format.fprintf ff "<ExDontCare>"

let value_to_string = Shared.Formatter_to_stringifier.f pp_print_value

let pp_print_unit_id ppf (Path s) =
  Format.fprintf ppf "%S" s

let read_caml_int s =
  let c = ref 0L in
  let sign, init =
    if String.length s > 0 && s.[0] = '-' then (-1L, 1) else (1L, 0)
  in
  let base, init =
    if String.length s >= init + 2 && s.[init] = '0'
    then
      ( (match s.[init + 1] with
        | 'x' | 'X' -> 16L
        | 'b' | 'B' -> 2L
        | 'o' | 'O' -> 8L
        | _ -> assert false),
        init + 2 )
    else (10L, init)
  in
  for i = init to String.length s - 1 do
    match s.[i] with
    | '0' .. '9' as x ->
      c := Int64.(add (mul base !c) (of_int (int_of_char x - int_of_char '0')))
    | 'a' .. 'f' as x ->
      c :=
        Int64.(
          add (mul base !c) (of_int (int_of_char x - int_of_char 'a' + 10)))
    | 'A' .. 'F' as x ->
      c :=
        Int64.(
          add (mul base !c) (of_int (int_of_char x - int_of_char 'A' + 10)))
    | '_' -> ()
    | _ ->
      Format.eprintf "FIXME literal: %s@." s;
      assert false
  done;
  Int64.mul sign !c

(* Untyped here. *)
let value_of_constant const =
  new_vtrace @@
  match const with
  | Pconst_integer (s, (None | Some 'l')) ->
    Int (Int64.to_int (read_caml_int s))
  | Pconst_integer (s, Some 'L') -> Int64 (read_caml_int s)
  | Pconst_integer (s, Some 'n') -> Nativeint (Int64.to_nativeint (read_caml_int s))
  | Pconst_integer (_s, Some c) ->
    Format.eprintf "Unsupported suffix %c@." c;
    assert false
  | Pconst_char c -> Int (int_of_char c)
  | Pconst_float (f, _) -> Float (float_of_string f)
  | Pconst_string (s, _) -> String (Bytes.of_string s)

let rec value_compare { v_ = v_1; _ } { v_ = v_2; _ } =
  match v_1, v_2 with
  | Bomb, _ -> raise BombExn
  | _, Bomb -> raise BombExn
  | Hole _, _ -> raise BombExn
  | _, Hole _ -> raise BombExn
  | Fun _, _
  | Function _, _
  | _, Fun _
  | _, Function _
  | Lz _, _
  | _, Lz _
  | Fun_with_extra_args _, _
  | _, Fun_with_extra_args _ ->
    raise BombExn
  | ModVal _, _ | _, ModVal _ -> raise BombExn
  | InChannel _, _ | OutChannel _, _ | _, InChannel _ | _, OutChannel _ ->
    raise BombExn
  | Fexpr _, _ | _, Fexpr _ -> raise BombExn
  | Prim _, _ | _, Prim _ -> raise BombExn
  | Object _, _ | _, Object _ -> raise BombExn

  | Int n1, Int n2 -> compare n1 n2
  | Int _, _ -> assert false

  | Int32 n1, Int32 n2 -> compare n1 n2
  | Int32 _, _ -> assert false

  | Int64 n1, Int64 n2 -> compare n1 n2
  | Int64 _, _ -> assert false

  | Nativeint n1, Nativeint n2 -> compare n1 n2
  | Nativeint _, _ -> assert false

  | Float f1, Float f2 -> compare f1 f2
  | Float _, _ -> assert false

  | String s1, String s2 -> compare s1 s2
  | String _, _ -> assert false

  | Constructor (_, _, None), Constructor (_, _, Some _) -> -1
  | Constructor (_, _, Some _), Constructor (_, _, None) -> 1
  | Constructor (c1, d1, vv1), Constructor (c2, d2, vv2) ->
    let c = compare (d1, c1) (d2, c2) in
    if c <> 0
    then c
    else (
      match (vv1, vv2) with
      | None, None -> 0
      | Some v1, Some v2 -> value_compare v1 v2
      | _ -> assert false)
  | Constructor _, _ -> assert false

  | Tuple l1, Tuple l2 ->
    assert (List.length l1 = List.length l2);
    List.fold_left2
      (fun cur x y -> if cur = 0 then value_compare x y else cur)
      0
      l1
      l2
  | Tuple _, _ -> assert false

  | Record r1, Record r2 ->
    let map1 =
      SMap.merge
        (fun _ u v ->
          match (u, v) with
          | None, None -> None
          | None, Some _ | Some _, None -> assert false
          | Some u, Some v -> Some (!u, !v))
        r1
        r2
    in
    SMap.fold
      (fun _ (u, v) cur -> if cur = 0 then value_compare u v else cur)
      map1
      0
  | Record _, _ -> assert false

  | Array a1, Array a2 ->
    let comp_len = compare (Array.length a1) (Array.length a2) in
    if comp_len <> 0 then comp_len
    else (
      let cmp = ref 0 in
      let count = ref 0 in
      while !cmp = 0 && !count < Array.length a1 do
        cmp := value_compare a1.(!count) a2.(!count);
        incr count
      done;
      !cmp
    )
  | Array _, _ -> assert false

  | ExCall _, _
  | _, ExCall _ ->
    failwith "tried to compare ExCall"

  | ExDontCare, _ ->
    failwith "tried to compare ExDontCare"


let value_equal v1 v2 = value_compare v1 v2 = 0

let value_lt v1 v2 = value_compare v1 v2 < 0
let value_le v1 v2 = value_compare v1 v2 <= 0
let value_gt v1 v2 = value_compare v1 v2 > 0
let value_ge v1 v2 = value_compare v1 v2 >= 0

let next_exn_id =
  let last_exn_id = ref (-1) in
  fun () ->
    incr last_exn_id;
    !last_exn_id

exception No_module_data
let get_module_data loc = function
  | Module data -> data
  | Functor _ ->
     Format.eprintf "%a@.Tried to access the components of a functor@."
       Location.print_loc loc;
     raise No_module_data
  | Unit (unit_id, unit_state) ->
     begin match !unit_state with
       | Initialized data -> data
       | exception Not_found ->
          Format.eprintf "%a@.Tried to access the undeclared unit %a@."
           Location.print_loc loc
           pp_print_unit_id unit_id;
          raise No_module_data
       | Not_initialized_yet ->
          Format.eprintf "%a@.unit %a is not yet initialized@."
            Location.print_loc loc
            pp_print_unit_id unit_id;
          raise No_module_data
     end

let module_name_of_unit_path path =
  path
  |> Filename.basename
  |> Filename.remove_extension
  |> String.capitalize_ascii

let inspect_vtrace (vtrace : vtrace) =
  let open Shared.Util in
  let string_of_tp_type (tp_type : tp_type) =
    match tp_type with
    | Intro -> "Intro"
    | Use -> "Use"
    | Ret -> "Ret"
    | PatMatch (_root_v, _projections) -> "PatMatch..."
  in
  let string_of_entry ((frame_no, loc), tp_type) =
    "((" ^ string_of_int frame_no ^ "," ^ Shared.Ast.Loc.to_string loc ^ ")," ^ string_of_tp_type tp_type ^ ")"
  in
  "[" ^ String.concat ";" (vtrace |>@ string_of_entry) ^ "]"