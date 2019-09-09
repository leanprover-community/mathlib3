/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

/-!
Replacement for the definition of `well_founded_tactics.default_dec_tac` in core.
-/

namespace well_founded_tactics
open tactic

/--
The definition of `default_dec_tac` in core is broken, because `unfold_sizeof`
could actually discharge the goal.

Here we add a test using `done` to detect this.
-/
meta def default_dec_tac' : tactic unit :=
abstract $
do clear_internals,
   unfold_wf_rel,
   process_lex (unfold_sizeof >> (done <|> (cancel_nat_add_lt >> trivial_nat_lt)))
end well_founded_tactics

/--
The default `well_founded_tactics` provided in core are broken in some situations, often indicated
by the message
```
The nested exception contains the failure state for the decreasing tactic.
nested exception message:
tactic failed, there are no goals to be solved
state:
no goals
```

Use this replacement by adding
```
using_well_founded wf_tacs
```
at the end of your inductive definition.
-/
meta def wf_tacs : well_founded_tactics :=
{ dec_tac := well_founded_tactics.default_dec_tac' }
