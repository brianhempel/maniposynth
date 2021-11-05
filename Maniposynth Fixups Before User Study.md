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

  - [ ] support visualizers on them

- [ ] perhaps fun arg values should have a yellow background? (or for the current frame at least?)

- [ ] rework layout alg

- [ ] insert case splits without extracting

- [x] gray out hole val to emphasize that it's different than hole exp

- [ ] still offering too many values for autocomplete

- [ ] highlight var value origins on hover

- [x] highlight holes in red

- [ ] tools offscreen

- [ ] tooltips describing what the pieces are?

- [ ] don't allow same names in a scope?

- [ ] two ret values displayed for `List.rev @@ x:: List.rev list`

- [ ] click out of expression editor with only a space caused an `undefined` to be inserted

- [ ] show type errors

- [ ] hide hints once there's stuff

- [ ] try colors only for same name/value; mouseover dims all other colors (what if value has multiple names...same color?)

- [x] too easy to switch frame
- [x] align values coming into function, one frame per column
- [x] click to switch frame?
- [ ] automatically visualize recurse calls and rets
- [ ] "new function" tool
- [ ] "add arg" tool
- [ ] "add example" tool (for function)
- [ ] legend explaining TV parts?
- [ ] allow comments
- [x] double-click to insert code should position the new TV
- [x] autocomplete with trees is UUUUUGGGGLLLYYY
- [ ] ensure tool works if subdirs have spaces
- [x] placing left and right extraction vbs was not working
- [x] bigger things not pushing smaller things out of the way
- [x] represent func values as unapplied val tools? Make sure they always insert calls
- [ ] divergence produces junk frames: combine identical frames?
- [ ] click on canvas vals to insert code into textbox
- [ ] setting to hide vals in exp labels?
- [ ] annoying "Serialization failure (): output_value: abstract value (Custom)" cluttering logs
- [ ] synth!
- [ ] hovering over scrutinee shows tooltip for entire match (because it's an exp, which we don't show tooltips for, but it's a the child of the match elem, which we are showing tooltips for)
- [ ] parans for vals?
- [ ] show type errors?
- [ ] add submit button for all textboxes (with hotkey noted)?
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

