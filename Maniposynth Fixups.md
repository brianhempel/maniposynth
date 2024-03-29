# Maniposynth Fixups

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

- [x] tool log output is getting noisy...something with asserts...??

- [x] statistics for synth

- [x] synth: fails with "F-expr failure" on

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

- [x] `x = y` only converts to assert at the top level, otherwise is a conditional

- [x] synth exceptions...sometimes the added type annotations can't be converted back to type exprs???

- [x] first top-level `x=y` accidentally inserted as binding rather than assert

- [x] synth: only accept expressions where all function vars are used

- [x] synth: only accept expressions where all branches exercised

- [ ] by default, position pat TVs in the order they appear in code

- [ ] match in ITE conditional position should float to outside

- [ ] inserting nested patterns in one go (via autocomplete) produced duplicate names (nat_max)

- [ ] did actually need to see some of the elided example cases (shuffles, bstd_valid)

- [ ] sometimes can't choose a specific type under which to synth because function is already used elsewhere at an incompatible type (i think we *can* do subtyping via unification: if one type doesn't change under unification then it was a subtype) this caused trouble with P1's insert_into_sorted_list helper (synth should have been able to fill the then and else clause)

- [ ] type errors shouldn't stop all edits...not sure how to do this

- [ ] type errors should not cover up the inspector

- [ ] more little labels instead of just colors: blue "Expected: " black "Got:" green "Assert satisfied:"

- [ ] ITE lines need more vertical space between them

- [ ] synthesis runs before the button pressed

- [ ] nested pat matches: drag-to-extract does wrong thing here, but dragging the existing pat names works:

  ```ocaml
  type 'a btree = Node of 'a btree * 'a * 'a btree | Empty
  
  let ex_tree =
    Node (Node (Empty, 0, Node (Empty, 0, Empty)), 0, Empty)
    [@@pos 820, 121]
  
  let rec btree_same_shape tree1 tree2 =
    let btree_same2 = btree_same_shape (??) (??) [@@pos 477, 22] in
    match tree1 with
    | Node (l1, _, r1) -> (
        match tree2 with
        | Node (l2, _, r2) ->
            let btree_same = btree_same_shape l1 l2 [@@pos 108, 0] in
            (??)
        | Empty -> (??) )
    | Empty -> (??)
    [@@pos 541, 396]
  
  let () =
    assert (btree_same_shape ex_tree (Node (Empty, 0, Empty)) = false)
    [@@pos 1927, 173]
  ```

  

- [x] popup explaining syntax error

- [x] draw if-then-else on multiple lines?

- [x] synth: prims should be typed for synth

- [x] exp extract labels shouldn't show attrs

- [x] remove `[@not ]` attrs when a hole is manually filled

- [ ] positioning: global update after movement? (so things never snap back?)

- [ ] tree exp constants should be prettified

- [ ] list exp constants should be large, then we can hide results for constants

- [ ] root value still needs more clickable area. I think that's a large part of why it feels like the tool isn't about value manipulation...too hard to dodge the children with the mouse

- [ ] asserts should be editable in the frames table

- [ ] better names for inserted calls...(from expression names??)

- [ ] click on unreachable base case should add assert that reaches that case

- [ ] divergence produces junk frames: combine identical frames?

- [ ] text edit in-place, instead of in inspector—and just highlight the clicked subexp

- [ ] autocomplete constants for examples

- [ ] synth: should trying using bindings that are after the holes!

- [ ] autocomplete: clicking a value on screen should add to autocomplete

- [ ] autocomplete: clicking a result option should not submit the textbox

- [ ] type errors should not cover up expressions (happens when expression is multiple lines)

- [ ] ~~synth: actually say in the interface if it timed out~~

- [ ] blue expected values should display as trees

- [ ] asserts should display prettified, editable trees

- [ ] selected exps (etc?) need a slightly different color background, not just a blue glow.

- [ ] synth: don't use `< <= > >=` at bool type (lol)

- [ ] synth: let user decide kinds of terms are allowed

- [ ] match scrutinee should be green so that it feels more clickable

- [x] delete on green result values

- [ ] rich text paste into textbox shouldn't cause mad trouble (I think nbsps are happening)

- [ ] "new function" tool

- [ ] "add arg" tool

- [x] add `< <= > >=` tools

- [x] add (||) and (&&) tools

- [ ] vis on tree in fun params not showing in the right place (P1S2 1:26:05)

- [x] render primitives

- [x] "add example" tool (for function)

- [x] autocomplete in rets should allow autocomplete to TVs in function body

- [ ] autocomplete should show exps and vals

- [ ] undo remembers text edit steps

- [ ] tools offscreen

- [ ] way to distinguish "x = y" between adding an assert, an equality, or a let-binding (suddenly display a dropdown when " = " is typed?)

- [x] accept/reject button for each synth filling

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

- [ ] autocomplete to vised values? nooo too many...or maybe root vised values only

- [ ] "done" button appears when func has no holes, to hide the function canvas/rets?


