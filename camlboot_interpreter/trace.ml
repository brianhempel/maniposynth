open Shared.Util

type trace_place = Location.t * int (* (ast id, frame_no) *)

module Entry = struct
  type t = Location.t * int * Data.value * Data.env (* (ast id, frame_no, value, env) *)

  let loc (loc, _, _, _)           = loc
  let frame_no (_, frame_no, _, _) = frame_no
  let value (_, _, value, _)       = value
  let env (_, _, _, env)           = env
end

type t =
  { entries : Entry.t list
  ; mutable by_frame_no : Entry.t list IntMap.t option
  ; mutable by_loc      : Entry.t list Shared.Loc_map.t option
  }

type trace_state =
  { mutable trace    : t
  ; mutable frame_no : int
  }

let empty =
  { entries     = []
  ; by_frame_no = None
  ; by_loc      = None
  }

let new_trace_state () =
  { trace = empty
  ; frame_no = 0
  }

let add entry trace =
  { empty with entries = entry :: trace.entries }

let entries_for_locs locs trace =
  let open Shared in
  let by_loc =
    (* Index, if we haven't yet *)
    match trace.by_loc with
    | Some by_loc -> by_loc
    | None ->
      let by_loc =
        trace.entries
        |> List.fold_left begin fun by_loc entry ->
          Loc_map.add_to_key (Entry.loc entry) entry by_loc
        end Loc_map.empty
      in
      trace.by_loc <- Some by_loc;
      by_loc
  in
  locs
  |>@@ (fun loc -> Loc_map.all_at_key loc by_loc)

let entries_for_loc loc trace =
  entries_for_locs [loc] trace

let entries_in_frame frame_no trace =
  let by_frame_no =
    (* Index, if we haven't yet *)
    match trace.by_frame_no with
    | Some by_frame_no -> by_frame_no
    | None ->
      let by_frame_no =
        trace.entries
        |> List.fold_left begin fun by_frame_no entry ->
          IntMap.add_to_key (Entry.frame_no entry) entry by_frame_no
        end IntMap.empty
      in
      trace.by_frame_no <- Some by_frame_no;
      by_frame_no
  in
  IntMap.all_at_key frame_no by_frame_no
