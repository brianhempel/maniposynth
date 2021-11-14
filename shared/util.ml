(* Convenience methods and filling in missing bits of the Stdlib. *)

module MapPlus (Key : sig type t val compare : t -> t -> int val to_string : t -> string end) = struct
  include Map.Make (Key)

  let keys   map = bindings map |> List.map fst
  let values map = bindings map |> List.map snd
  let remove_all keys = List.fold_right remove keys

  let to_string val_to_string smap =
    bindings smap
    |> List.map (fun (k, v) -> Key.to_string k ^ " => " ^ val_to_string v)
    |> String.concat ",\n"
    |> fun str -> "{\n" ^ str ^ "}"

  let of_list list = list |> List.fold_left (fun smap (k, v) -> add k v smap) empty
end

module SMap   = MapPlus (struct include String let to_string s = s end)
module IntMap = MapPlus (struct type t = int let compare = compare let to_string = string_of_int end)


module SetPlus (Key : sig type t val compare : t -> t -> int end) = struct
  include Set.Make (Key)

  let add_all    elems = List.fold_right add elems
  let remove_all elems = List.fold_right remove elems

  let union_all sets = List.fold_right union sets empty
end

module SSet    = SetPlus (String)
module IntSet  = SetPlus (struct type t = int let compare = compare end)
module CharSet = SetPlus (Char)

let clamp lo hi x =
  if x < lo then lo
  else if x > hi then hi
  else x

(* Default for Option, like (null || default) in other languages *)
let (||&) opt default = match opt with Some x -> x | _ -> default
(* Rightward compose default for Option *)
let (%||&) f default = fun x -> match f x with Some x -> x | _ -> default

(* Lazy default *)
let (||&~) opt default_f = match opt with Some x -> x | _ -> default_f ()
(* Rightward compose lazy default for Option *)
let (%||&~) f default_f = fun x -> match f x with Some x -> x | _ -> default_f ()


module Option = struct
  (* Selections from https://ocaml.org/api/Option.html *)
  let some x = Some x
  let map f = function Some x -> Some (f x) | None -> None
  let iter f = function Some x -> f x | None -> ()
  let join = function Some (Some x) -> Some x | _ -> None
  let to_list = function Some x -> [x] | None -> []

  let rec project = function
    | []             -> Some []
    | None   :: _    -> None
    | Some x :: rest -> project rest |> map (List.cons x)
end

module Tup2 = struct
  let map_fst f (x, y) = (f x, y)
  let map_snd f (x, y) = (x, f y)
end

module Tup3 = struct
  let fst (x, _, _) = x
  let snd (_, x, _) = x
  let thd (_, _, x) = x
  let map_fst f (x, y, z) = (f x, y, z)
  let map_snd f (x, y, z) = (x, f y, z)
  let map_thd f (x, y, z) = (x, y, f z)
end

module Tup4 = struct
  let fst (x, _, _, _)  = x
  let snd (_, x, _, _)  = x
  let thd (_, _, x, _)  = x
  let frth (_, _, _, x) = x
  let map_fst f (x, y, z, u)  = (f x, y, z, u)
  let map_snd f (x, y, z, u)  = (x, f y, z, u)
  let map_thd f (x, y, z, u)  = (x, y, f z, u)
  let map_frth f (x, y, z, u) = (x, y, z, f u)
end

module List = struct
  include List

  let singleton x = [x]

  (* List.for_all2 but returns false when lists have different lengths *)
  let for_all2_safe pred xs ys =
    try for_all2 pred xs ys
    with Invalid_argument _ -> false

  let hd_opt = function
    | []   -> None
    | x::_ -> Some x

  let rec last = function
    | []      -> raise (Invalid_argument "List.last called on empty list")
    | [x]     -> x
    | _::rest -> last rest

  let rec last_opt = function
    | []      -> None
    | [x]     -> Some x
    | _::rest -> last_opt rest

  let rec prefix len list =
    if len <= 0 then [] else
    match list with
    | []      -> list
    | x::rest -> x :: prefix (len-1) rest

  let rec drop len list =
    if len <= 0 then list else
    match list with
    | []      -> list
    | _::rest -> drop (len-1) rest

  let suffix len list = drop (length list - len) list

  let take_while pred list =
    let rec loop out list =
      match list with
      | x::rest when pred x -> loop (x::out) rest
      | _                   -> out
    in
    loop [] list

  let rec replace_nth i new_elem = function
    | [] -> raise (Invalid_argument "List.replace_nth called on a list that is too short")
    | x::rest ->
      if i = 0
      then new_elem :: rest
      else x :: replace_nth (i-1) new_elem rest

  let findi_opt pred list =
    let rec loop i = function
      | []      -> None
      | x::rest -> if pred x then Some i else loop (i + 1) rest
    in
    loop 0 list

  let findi pred list =
    match findi_opt pred list with
    | None   -> raise Not_found
    | Some i -> i

  let rec findmap_opt f = function
    | []      -> None
    | x::rest ->
      begin match f x with
      | None   -> findmap_opt f rest
      | some_y -> some_y
      end

  let concat_map f list =  map f list |> concat

  let rec count pred = function
    | [] -> 0
    | x::xs when pred x -> 1 + count pred xs
    | _::xs             -> count pred xs

  let rec assoc_by_opt pred = function
    | [] -> None
    | (k, v)::rest ->
      if pred k then Some v
      else assoc_by_opt pred rest

  let diff xs items_to_remove =
    xs |> filter (fun x -> not (mem x items_to_remove))

  (* Intersection *)
  let inter xs ys =
    xs |> filter (fun x -> mem x ys)

  let any_overlap xs ys =
    xs |> exists (fun x -> mem x ys)

  (* Removes first *)
  let rec remove x = function
    | []                 -> []
    | y::rest when x = y -> rest
    | y::rest            -> y :: remove x rest

  let remove_all x = filter ((<>) x)

  (* List already has sort_uniq *)
  (* This preserves order. *)
  let dedup list =
    let rec dedup_ out = function
      | [] -> rev out
      | x::rest ->
        if List.mem x out
        then dedup_ out rest
        else dedup_ (x :: out) rest
    in
    dedup_ [] list

  let dedup_by f list =
    let rec dedup_ seen out = function
      | [] -> rev out
      | x::rest ->
        let v = f x in
        if List.mem v seen
        then dedup_ seen out rest
        else dedup_ (v :: seen) (x :: out) rest
    in
    dedup_ [] [] list

  let sort_by f list =
    list
    |> map (fun elem -> (f elem, elem))
    |> sort (fun (a, _) (b, _) -> compare a b)
    |> map snd

  (* returns (stuff, replacement_func) option *)
  (* replacement_func takes a list to insert at the extraction location *)
  let extractmap_opt f list =
    let rec loop before_rev = function
      | [] -> None
      | x::rest ->
        begin match f x with
        | Some stuff -> Some (stuff, fun sublist -> List.rev before_rev @ sublist @ rest)
        | None -> loop (x::before_rev) rest
        end
    in
    loop [] list

  (* returns (elem, replacement_func) option *)
  (* replacement_func takes a list to insert at the extraction location *)
  let extract_by_opt pred list =
    extractmap_opt (fun x -> if pred x then Some x else None) list

  (* returns (elem, replacement_func) option *)
  (* replacement_func takes a list to insert at the extraction location *)
  let extract_opt target list =
    extract_by_opt ((=) target) list

  let max = function
    | x::xs -> List.fold_left max x xs
    | []    -> raise @@ Invalid_argument "List.max needs to be given a non-empty list"

  let min = function
    | x::xs -> List.fold_left min x xs
    | []    -> raise @@ Invalid_argument "List.max needs to be given a non-empty list"
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

module Char = struct
  include Char

  let is_capital c = 'A' <= c && c <= 'Z'
  let is_lower c = 'a' <= c && c <= 'z'
  let is_letter c = is_lower c || is_capital c
  let is_number c = '0' <= c && c <= '9'
  let is_alphanum c = is_letter c || is_number c
end

module String = struct
  include String

  (* Like String.sub but does not error for ranges outside the string. *)
  let safe_sub i len str =
    let safe_i = clamp 0 (String.length str) i in
    let safe_j = clamp 0 (String.length str) (i + len) in
    sub str safe_i (safe_j - safe_i)

  let prefix len str = Str.first_chars str len
  let suffix len str = Str.last_chars str len

  let drop len str = suffix (length str - len) str

  (* Tail recursive string matcher to see if target containts str at the given indices. *)
  let rec matches_at_indices_ str_i target target_i target_len str =
    if target_i >= target_len then
      true
    else if unsafe_get str str_i = unsafe_get target target_i then
      matches_at_indices_ (str_i + 1) target (target_i + 1) target_len str
    else
      false

  let matches_at_index str_i target str =
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

  let drop_suffix suffix str =
    if ends_with suffix str
    then prefix (length str - length suffix) str
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

  let includes target str : bool =
    find_index target str <> None


  let whitespace_regex = Str.regexp "[ \n\r\t\012]+"
  let split_on_regex ?limit regex str =
    match  limit with
    | None       -> Str.split_delim         regex str
    | Some limit -> Str.bounded_split_delim regex str limit

  let split_on_regex_str  ?limit regex_str str = split_on_regex ?limit (Str.regexp regex_str)  str
  let split               ?limit sep       str = split_on_regex ?limit (Str.regexp_string sep) str
  let split_on_whitespace ?limit           str = split_on_regex ?limit whitespace_regex        (String.trim str)

  let replace target replacement str =
    split target str |> String.concat replacement

  let to_list str = str |> to_seq |> List.of_seq
  (* Show non-printable chars, so we can see what went wrong somewhere *)
  let inspect str = str |> to_list |> List.map Char.escaped |> concat ""
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
let (|>@@) list f = List.concat_map f list
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

(* Leftward compositon (like @@, follows the above pattern of replacing the first char with %) *)
let (%@) g f = f %> g


let executable_dir = Filename.dirname Sys.executable_name
let nativize_path = String.replace "/" Filename.dir_sep

let rec ensure_dir path =
  if Filename.dirname path <> "." && Filename.dirname path <> "/" then ensure_dir (Filename.dirname path);
  try if Filename.basename path <> "." && Filename.basename path <> "/" then Unix.mkdir path 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()

(* https://stackoverflow.com/a/53840784 *)
let string_of_file path =
  let in_chan = open_in path in
  let str = really_input_string in_chan (in_channel_length in_chan) in
  close_in in_chan;
  str

let write_file contents path =
  ensure_dir (Filename.dirname path);
  let out_chan = open_out path in
  output_string out_chan contents;
  close_out out_chan
