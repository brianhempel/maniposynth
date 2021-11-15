# Maniposynth Fixups Before User Study

- [x] make sure it can be installed on mac/windows/linux

- [x] post the recruitment survey

- [x] coloring of autocomplete values is off

- [x] don't change frame_no when autocomplete open

- [ ] autocomplete to value: sort by 2D distance on canvas? or by scope distance?

- [x] slightly better naming?

- [x] when dragging length into itself, divergence is confusing

- [x] need to reflow absolutely positioned elements

- [x] autocomplete state left on when deselecting a box

- [x] autocomplete left open when clicking away from a new code entry

- [x] color TV results background

- [ ] ~~text edit a binding to a var in a branch didn't work~~

  ```ocaml
  let ... = length (??) (* changed (??) to x *)
  match ... with 
  | ... -> let x = ... in
  ```

  wait now it works....why????

- [x] edit values (associated expression)

- [x] drag exp to value position

- [x] defocus to save (rather than enter)

- [x] don't insert nested defs for missing vars

- [x] differing semantics for use/vis ... deactivate use

- [x] hover border for movable boxes

- [x] selecting vis shouldn't show submit buttons

- [x] tooltips showing exp for visualizer, on hover

- [x] ...x more... math is wrong

- [x] don't color vised values (can't autocomplete to them yet)

- [x] parens for exps

- [x] less space for tree fold

- [x] bake undo into the server

- [x] ensure it can run without ocamlformat

- [x] ensure it can run without ruby

- [x] preserve frame across changes

- [x] trees were only drawing for the first tree

- [x] 0 in terminal Leaf 0 is not available for autocomplete

  ```ocaml
  type 'a tree = Node of 'a tree * 'a tree | Leaf of 'a
  
  let tree = Node (Node (Leaf 0, Leaf 0), Leaf 0) [@@pos 552, 539]
  
  let rec fold f acc tree =
    match tree with
    | Node (a_tree, a_tree2) ->
        let fold_f = fold f acc a_tree2 [@@pos 20, 46] in
        let fold2 = fold f fold_f a_tree [@@pos 562, 39] in
        (??)
    | Leaf a -> f
  
  let fold_List_cons_tree = fold List.cons [] tree [@@pos 143, 641]
  ```

  actually, this is a pretty deep problem

  - [x] disallow autocomplete to values in higher scope
  - [x] assign "value ids" unique per thing displayed on the screen rather than via tracing

- [x] don't allow drag onto self

- [x] make exps bigger?

- [x] align exp labels on TVs so it looks more like cells

- [x] display label as `pat = exp`

- [x] show infix op result on infix op

- [x] placeholder on function canvas to prompt?

- [x] show case pats as TVs on canvas

- [x] and don't insert superfluous bindings that show the same thing

- [x] fix undo/redo

- [x] only allow direct value edits on constants in the immediate expression

- [x] bigger click targets for root exps

- [x] indicate that you're editing an exp

- [x] shorter names, name constants by type

- [x] display rets as a row under the incoming function args

  - [x] ~~support visualizers on them~~

- [x] perhaps fun arg values should have a yellow background? (or for the current frame at least?)

- [x] rework layout alg

- [x] insert case splits without extracting

- [x] gray out hole val to emphasize that it's different than hole exp

- [x] hard-code `hd::tail` names for list

- [x] destruct should work at the top level...

- [x] still offering too many values for autocomplete

- [x] highlight holes in red

- [x] try making holes bigger

- [x] need to resize top-level canvas vertically so you can double-click to add code when scrolled down

- [x] typing boolean expression at top level produces an assert

- [x] allow multi-arg asserts

- [x] create new bindings near old bindings

- [x] new top-level bindings should be *last* by default, not immediately before last

- [x] assert on TV result (but top-level only for now)

- [x] undo doesn't work with synth

- [x] key command for synth

- [x] fix synth hanging

- [x] setting to hide vals in exp labels

- [x] vertical movement is now offffffff

- [x] trim down the synth env

- [x] fixup new assert positioning

- [x] show type errors

- [x] don't crash on un-recoverable type error

- [x] blue expected values should display in the right places

- [ ] divergence produces junk frames: combine identical frames?

- [ ] "new function" tool

- [ ] "add arg" tool

- [x] tool log output is getting noisy...something with asserts...??

- [x] statistics for synth

- [ ] synth: fails with "F-expr failure" on

  ```ocaml
  let map list f =
    match list with
    | hd :: tail ->
        let f2 = f hd [@@pos 212, 32] in
        (??)
    | [] -> []
    [@@pos 367, 87]
  
  let () =
    assert (map [ 1; 2; 3 ] string_of_int = [ "1"; "2"; "3" ])
    [@@pos 817, 97]
  
  let () = assert (map [ "1"; "2" ] int_of_string = [ 1; 2 ]) [@@pos 874, 214]
  
  let () = assert (map [] int_of_string = []) [@@pos 965, 402]
  ```

  also doesn't synth when given only tail. (works if you give both)

- [x] synth: for fold, I don't think the synthesizer trying the higher order function `f` in function position (type is `'a` I think) simpler example:

  ```ocaml
  type nat = Z | S of nat
  
  let rec map f list =
    match list with hd :: tail -> (??) :: map f tail | [] -> []
    [@@pos 0, 234]
  
  let () =
    assert (map (fun x -> x + 3) [ 1; 2; 3 ] = [ 4; 5; 6 ])
    [@@pos 271, 244]
  
  let () = assert (map succ [ 1; 2; 3 ] = [ 2; 3; 4 ]) [@@pos 581, 387]
  ```

  

- [x] synth: also not smart about types of return exps

- [x] synth: multiple contradictory reqs on hole should always guess non-constants

- [x] synth: single req on hole should only guess the constant in the req

- [ ] synth: should trying using bindings that are after the holes!

- [ ] ~~synth: actually say in the interface if it timed out~~

- [ ] synth: don't use `< <= > >=` at bool type (lol)

- [ ] text edit in-place, instead of in inspector—and just highlight the clicked subexp

- [ ] delete on green result values

- [x] add (||) and (&&) tools

- [ ] vis on tree in fun params not showing in the right place (P1S2 1:26:05)

- [x] render primitives

- [x] "add example" tool (for function)

- [ ] autocomplete constants for examples

- [ ] autocomplete should show exps and vals

- [ ] undo remembers text edit steps

- [ ] tools offscreen

- [x] accept/reject button for each synth filling

- [ ] way to distinguish "x = y" between adding an assert, an equality, or a let-binding (suddenly display a dropdown when " = " is typed?)

- [ ] shouldn't be able to drag values from out of frame

- [ ] allow typing "let x = e" at non-top-level

- [ ] inline?

- [ ] destruct button hard to hit when TVs close together

- [ ] val superscripts are wrong color in return exps

- [ ] vis pane shouldn't show for selected val superscripts

- [ ] tooltips describing what the pieces are?

- [ ] don't allow same names in a scope?

- [ ] two ret values displayed for `List.rev @@ x:: List.rev list`

- [ ] click out of expression editor with only a space caused an `undefined` to be inserted

- [ ] highlight var value origins on hover

- [ ] hide hints once there's stuff

- [ ] pink subvalue names should not show out-of-scope

- [ ] use types to be smarter about type of dragged function (whether it should be a call or not)

- [ ] type-directed drag-to-hole?

- [ ] click branch return that isn't hit yet: auto-gen an example that hits it? (Otherwise you can't double-click edit that expression!)

- [ ] I still feel like it's hard to tell the branch returns apart from each other...show those pats all the time?

- [ ] try colors only for same name/value; mouseover dims all other colors (what if value has multiple names...same color?)

- [x] too easy to switch frame

- [x] align values coming into function, one frame per column

- [x] click to switch frame?

- [ ] automatically visualize recurse calls and rets

- [ ] legend explaining TV parts?

- [ ] allow comments

- [x] double-click to insert code should position the new TV

- [x] autocomplete with trees is UUUUUGGGGLLLYYY

- [ ] ensure tool works if subdirs have spaces

- [x] placing left and right extraction vbs was not working

- [x] bigger things not pushing smaller things out of the way

- [x] represent func values as unapplied val tools? Make sure they always insert calls

- [ ] click on canvas vals to insert code into textbox

- [x] annoying "Serialization failure (): output_value: abstract value (Custom)" cluttering logs

- [x] Maniposynth mission statement as the top-level background?

- [ ] hovering over scrutinee shows tooltip for entire match (because it's an exp, which we don't show tooltips for, but it's a the child of the match elem, which we are showing tooltips for)

- [ ] animate layout changes? (clunky because involves page reload)

- [ ] parans for vals?

- [ ] show destruct button on relevant patterns as well?

- [ ] add submit button for all textboxes (with hotkey noted)? participants don't have a problem with this

- [ ] autocomplete to vised values?

- [ ] "done" button appears when func has no holes, to hide the function canvas/rets?





## study

- [x] build tool
- [x] email zoom link
- [x] record consent
- [x] stop recording
- [ ] setup payment https://finserv.uchicago.edu/sites/finserv.uchicago.edu/files/uploads/Form%20W-9%20%28Rev.%20October%202018%29.pdf
- [x] email w9
- [ ] email tool & vim/emacs directions
- [ ] record

