# Synth Stats Model

Modified Camlboot interpreter again, because want to be able to keep careful track of where values came from in the presence of module opens, and careful track of the order of variable definitions (execution env is now a *list* instead of a map, most recently introduced items first.)

The `eval` functions have been modified to not really eval (they don't apply functions) but instead collect stats about variable usage.

## Variable usage patterns

1. All var usages that resolve to a var in an open module are considered to be their fully qualified version (e.g. `Stdlib.List.map` even in the presence of `open List`)

2. When a pattern introduces a value ident, we enter it into the environment, marked unused (no most recent use loc).

3. When encountering a variable usage, it is classified as follows:

   FOR UNQUALIFIED VARS:

   1. If the variable is unused, we count the number of unused vars before it in the env and mark the var as first use of the nth unused variable. The var in the env is mutably marked with the current loc as its most recent use.
   2. If the variable is used, we sort the env variables by most recent use locations and mark the var as a copy of nth most recently used variable. The the var in the env is mutably marked with the current loc as its most recent use.

   FOR QUALIFIED VARS:

   3. The var is marked as a use of the full qualified name.

4. On module open, the variables from the module added to the environment are marked as having come from that module name.

At the end, all these uses are gathered up.

(Perhaps distinguish between vars usages in function position vs. not?)

## Constants

Terms of size <=7 with no free variables are considered constant. Constructor names and pervasive names are not considered free variables. We gather these up.

