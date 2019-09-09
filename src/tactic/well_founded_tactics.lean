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

The usual symptom is an error message
```
The nested exception contains the failure state for the decreasing tactic.
nested exception message:
tactic failed, there are no goals to be solved
state:
no goals
```

Use this replacement by adding
```
using_well_founded { dec_tac := well_founded_tactics.default_dec_tac' }
```
at the end of your inductive definition.
-/
-- Here we add a test using `done` to detect this.
meta def default_dec_tac' : tactic unit :=
abstract $
do clear_internals,
   unfold_wf_rel,
   process_lex (unfold_sizeof >> (done <|> (cancel_nat_add_lt >> trivial_nat_lt)))
end well_founded_tactics
