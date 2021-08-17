
module IMap = Map.Make (struct type t = int let compare : int -> int -> int = compare end) (* https://stackoverflow.com/questions/10131779/ocaml-map-of-int-keys-where-is-the-simple-int-module-to-use-with-the-map-ma/10132568#comment13019626_10132568 *)

type trace_place = Location.t * int (* (ast id, frame_no) *)

module Entry = struct
  type t = Location.t * int * Data.value * Data.env (* (ast id, frame_no, value, env) *)

  let loc (loc, _, _, _)           = loc
  let frame_no (_, frame_no, _, _) = frame_no
  let value (_, _, value, _)       = value
  let env (_, _, _, env)           = env
end

type t = Entry.t IMap.t

type trace_state =
  { mutable trace    : t
  ; mutable frame_no : int
  }

let empty = IMap.empty

let new_trace_state =
  { trace = empty
  ; frame_no = 0
  }

let add entry trace =
  let counter = if IMap.is_empty trace then 0 else IMap.max_binding trace |> fst in
  IMap.add (counter + 1) entry trace

let entries_for_loc loc trace =
  let finder _ entry results =
    if Entry.loc entry = loc then
      entry :: results
    else
      results
  in
  IMap.fold finder trace []

let entries_in_frame frame_no trace =
  let finder _ entry results =
    if Entry.frame_no entry = frame_no then
      entry :: results
    else
      results
  in
  IMap.fold finder trace []

