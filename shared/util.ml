(* Convenience methods and filling in missing bits of the Stdlib. *)

let clamp lo hi x =
  if x < lo then lo
  else if x > hi then hi
  else x

let concat_map f list =  List.map f list |> List.concat

let partition pred list =
  List.fold_right
    (fun x (trues, falses) -> if pred x then (x::trues, falses) else (trues, x::falses))
    list
    ([], [])


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

module List = struct
  include List

  let rec last = function
    | []      -> raise (Invalid_argument "List.last called on empty list")
    | [x]     -> x
    | _::rest -> last rest

  let rec findmap_opt f = function
    | []      -> None
    | x::rest ->
      begin match f x with
      | None   -> findmap_opt f rest
      | some_y -> some_y
      end

  let dedup list =
    let rec dedup_ out = function
    | [] -> rev out
    | x::rest ->
      if List.mem x out
      then dedup_ out rest
      else dedup_ (x :: out) rest in
    dedup_ [] list
end

module Seq = struct
  include Seq

  (* OCaml 4.07.1 doesn't have Seq.append yet *)
  let rec append seq1 seq2 () =
    match seq1 () with
    | Seq.Nil             -> seq2 ()
    | Seq.Cons (x, seq1') -> Seq.Cons (x, append seq1' seq2)

  (* Don't even bother with the computation to initialize seq2 until seq1 is complete *)
  let rec append_lazy seq1 seq2_thunk () =
    match seq1 () with
    | Seq.Nil             -> seq2_thunk () ()
    | Seq.Cons (x, seq1') -> Seq.Cons (x, append_lazy seq1' seq2_thunk)

  let rec concat seqs =
    match seqs with
    | []        -> Seq.empty
    | seq::rest -> append seq (concat rest)

  (* Turn n sequences into a sequence that produces lists of n values of all possible combinations between sequences. *)
  let rec cart_prod seqs =
    match seqs with
    | seq1::rest ->
      seq1 |> Seq.flat_map begin fun elem1 ->
        cart_prod rest
        |> Seq.map (List.cons elem1)
      end
    | [] -> Seq.return []
end

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
