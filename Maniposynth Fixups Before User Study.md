# Maniposynth Fixups Before User Study

- [ ] make sure it can be installed on mac/windows/linux

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

- [ ] 0 in terminal Leaf 0 is not available for autocomplete

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

- [ ] the type for the tree task doesn't work right

- [ ] too easy to switch frame

- [ ] align values coming into function, one frame per column

- [ ] click to switch frame?

- [ ] display rets as a row under the incoming function args

- [ ] bake undo into the server

- [ ] highlight var value origins on hover

- [x] double-click to insert code should position the new TV

- [x] autocomplete with trees is UUUUUGGGGLLLYYY

- [ ] tools offscreen

- [ ] placeholder on function canvas to prompt

- [x] placing left and right extraction vbs was not working

- [ ] represent func valus as unapplied val tools?

- [ ] divergence produces junk frames: combine identical frames?

- [ ] click on canvas vals to insert code into textbox

- [ ] automatically visualize recurse calls and rets?

- [ ] highlight hole returns

- [ ] setting to hide vals in exp labels?

- [ ] annoying "Serialization failure (): output_value: abstract value (Custom)" cluttering logs

- [ ] synth!

- [ ] hovering over scrutinee shows tooltip for entire match (because it's an exp, which we don't show tooltips for, but it's a the child of the match elem, which we are showing tooltips for)

- [ ] parans for vals?

- [ ] show type errors?

- [ ] add submit button for all textboxes (with hotkey noted)?

- [ ] autocomplete to vised values?

- [ ] "done" button appears when func has no holes, to hide the function canvas/rets?

