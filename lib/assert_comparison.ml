open Camlboot_interpreter
open Shared.Util


exception Not_equal

let rec seen_before a b = function
  | []             -> false
  | (x, y) :: rest -> (a == x && b == y) || seen_before a b rest

(* Based on Camlboot_interpreter.Data.value_compare *)
(* May be called on arguments of incompatible type *)
(* Needs to be able to compare closures *)
(* Turn on "loose" for comparing closure environments. There are certain values captured in environments that we don't elsewhere support, so those are compared loosely. *)
(* The graph can have cycles, so keep track of the items compared down the callstack *)
let rec values_equal_for_assert ?(seen_v_s = []) ?(seen_envs = []) ?(seen_mods = []) ?(loose = false) (Data.{ v_ = v_1; _ } as _v1) (Data.{ v_ = v_2; _ } as _v2) =
  (* Data.pp_print_value Format.std_formatter v1;
  Data.pp_print_value Format.std_formatter v2; *)
  v_1 == v_2 || seen_before v_1 v_2 seen_v_s || (* Cycle. They're equal as far as this branch of execution is concerned. *)
  let seen_v_s = (v_1, v_2)::seen_v_s in
  let recurse = values_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods in
  let open Data in
  match v_1, v_2 with
  | Bomb, Bomb -> loose
  | Bomb, _ -> false
  | _, Bomb -> false

  | Fun (arg_label1, exp_opt1, pat1, exp1, env_ref1)
  , Fun (arg_label2, exp_opt2, pat2, exp2, env_ref2) ->
    arg_label1 = arg_label2 && exp_opt1 = exp_opt2 && pat1 = pat2 && exp1 = exp2 && envs_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods !env_ref1 !env_ref2
  | Fun _, _ -> false

  | Function (cases1, env_ref1)
  , Function (cases2, env_ref2) ->
    cases1 = cases2 && envs_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods !env_ref1 !env_ref2
  | Function _, _ -> false

  | ModVal mod1
  , ModVal mod2 -> mods_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods mod1 mod2
  | ModVal _, _ -> false

  | Lz _, Lz _ -> loose
  | Lz _, _ -> false

  | Fun_with_extra_args (v1, vs1, named_args1)
  , Fun_with_extra_args (v2, vs2, named_args2) ->
    (* These are only produced during the application of functions with labeled arguments *)
    SMap.cardinal named_args1 = SMap.cardinal named_args2 &&
    List.for_all2 recurse (v1::vs1) (v2::vs2) &&
    List.for_all2
      (fun (name1, (label1, v1)) (name2, (label2, v2)) -> name1 = name2 && label1 = label2 && recurse v1 v2)
      (SMap.bindings named_args1)
      (SMap.bindings named_args2)
  | Fun_with_extra_args _, _ -> false

  | Fexpr _, Fexpr _ -> loose (* there's only a few of these *)
  | Fexpr _, _ -> false

  | Prim _, Prim _ -> loose
  | Prim _, _ -> false

  | InChannel chan1, InChannel chan2 -> chan1 = chan2
  | InChannel _, _ -> false

  | OutChannel chan1, OutChannel chan2 -> chan1 = chan2
  | OutChannel _, _ -> false

  (* Woefully incomplete, but we don't support objects so it doesn't matter. *)
  | Object obj1, Object obj2 -> obj1.self = obj2.self && envs_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods obj1.env obj2.env
  | Object _, _ -> false

  | Int n1, Int n2 -> n1 = n2
  | Int _, _ -> false

  | Int32 n1, Int32 n2 -> n1 = n2
  | Int32 _, _ -> false

  | Int64 n1, Int64 n2 -> n1 = n2
  | Int64 _, _ -> false

  | Nativeint n1, Nativeint n2 -> n1 = n2
  | Nativeint _, _ -> false

  | Float f1, Float f2 -> f1 = f2 || f1 == f2 (* nan :D *)
  | Float _, _ -> false

  | String s1, String s2 -> s1 = s2
  | String _, _ -> false

  | Constructor (c1, d1, None),    Constructor (c2, d2, None)    -> (c1, d1) = (c2, d2)
  | Constructor (c1, d1, Some v1), Constructor (c2, d2, Some v2) -> (c1, d1) = (c2, d2) && recurse v1 v2
  | Constructor _, _ -> false

  | Tuple l1, Tuple l2 ->
    List.length l1 = List.length l2 && List.for_all2 recurse l1 l2
  | Tuple _, _ -> false

  | Record r1, Record r2 ->
    SMap.cardinal r1 = SMap.cardinal r2 &&
    SMap.for_all begin fun label vref1 ->
      match SMap.find_opt label r2 with
      | Some vref2 -> recurse !vref1 !vref2
      | None       -> false
    end r1
  | Record _, _ -> false

  | Array a1, Array a2 ->
    Array.length a1 = Array.length a2 &&
    begin
      let i      = ref 0 in
      let result = ref true in
      while !result && !i < Array.length a1 do
        result := recurse a1.(!i) a2.(!i);
        incr i
      done;
      !result
    end
  | Array _, _ -> false

  (* Surface syntax asserts should not deal with Ex values; so use strict comparison rather than "not caring" *)
  | ExDontCare, ExDontCare -> true
  | ExDontCare, _ -> false
  | ExCall (vl1, vr1), ExCall (vl2, vr2) -> recurse vl1 vl2 && recurse vr1 vr2
  | ExCall _, _ -> false

and envs_equal_for_assert ?(seen_v_s = []) ?(seen_envs = []) ?(seen_mods = []) env1 env2 =
  env1 == env2 || seen_before env1 env2 seen_envs || (* Cycle. They're equal as far as this branch of execution is concerned. *)
  let seen_envs = (env1, env2)::seen_envs in
  let open Data in
  try
    ignore @@ SMap.merge begin fun _name v1_opt v2_opt ->
      match v1_opt, v2_opt with
      | None, None -> None
      | Some (_, Value v1), Some (_, Value v2) ->
        ignore (values_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods ~loose:true v1 v2 || raise Not_equal); None
      | Some (_, Instance_variable _), Some (_, Instance_variable _) ->
        None (* ignore instance variables *)
      | _ -> raise Not_equal
    end env1.values env2.values;
    ignore @@ SMap.merge begin fun _name mod1_opt mod2_opt ->
      match mod1_opt, mod2_opt with
      | None, None -> None
      | Some (_, mod1), Some (_, mod2) ->
        ignore (mods_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods mod1 mod2 || raise Not_equal); None
      | _ -> raise Not_equal
    end env1.modules env2.modules;
    ignore @@ SMap.merge begin fun _name ctor_opt1 ctor_opt2 ->
      match ctor_opt1, ctor_opt2 with
      | None, None -> None
      | Some (_, int1), Some (_, int2) ->
        ignore (int1 = int2 || raise Not_equal); None
      | _ -> raise Not_equal
    end env1.constructors env2.constructors;
    (* Ignore classes *)
    (* Ignore current_object *)
    true
  with Not_equal -> false

and mods_equal_for_assert ?(seen_v_s = []) ?(seen_envs = []) ?(seen_mods = []) mod1 mod2 =
  mod1 == mod2 || seen_before mod1 mod2 seen_mods || (* Cycle. They're equal as far as this branch of execution is concerned. *)
  let seen_mods = (mod1, mod2)::seen_mods in
  let open Data in
  match mod1, mod2 with
  | Unit (_, { contents = Initialized mod_val1 })
  , Unit (_, { contents = Initialized mod_val2 })
  | Unit (_, { contents = Initialized mod_val1 })
  , Module mod_val2
  | Module mod_val1
  , Unit (_, { contents = Initialized mod_val2 })
  | Module mod_val1
  , Module mod_val2 ->
    begin try
      ignore @@ SMap.merge begin fun _name v1_opt v2_opt ->
        match v1_opt, v2_opt with
        | None, None -> None
        | Some v1, Some v2 ->
          ignore (values_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods ~loose:true v1 v2 || raise Not_equal); None
        | _ -> raise Not_equal
      end mod_val1.mod_values mod_val2.mod_values;
      ignore @@ SMap.merge begin fun _name mod1_opt mod2_opt ->
        match mod1_opt, mod2_opt with
        | None, None -> None
        | Some mod1, Some mod2 ->
          ignore (mods_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods mod1 mod2 || raise Not_equal); None
        | _ -> raise Not_equal
      end mod_val1.mod_modules mod_val2.mod_modules;
      SMap.bindings mod_val1.mod_constructors = SMap.bindings mod_val2.mod_constructors
      (* Ignore classes *)
    with Not_equal -> false end

  | Unit (_, { contents = Not_initialized_yet })
  , Unit (_, { contents = Not_initialized_yet }) ->
    true

  | Functor (name1, mod_exp1, env1)
  , Functor (name2, mod_exp2, env2) ->
    name1    = name2    &&
    mod_exp1 = mod_exp2 &&
    envs_equal_for_assert ~seen_v_s ~seen_envs ~seen_mods env1 env2

  | _ ->
    false