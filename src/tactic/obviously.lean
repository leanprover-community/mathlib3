/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.tidy
import tactic.replacer

namespace tactic

/--
`sorry_if_contains_sorry` will solve any goal already containing `sorry` in its type with `sorry`,
and fail otherwise.
-/
meta def sorry_if_contains_sorry : tactic unit :=
do
  g ← target,
  guard g.contains_sorry <|> fail "goal does not contain `sorrry`",
  tactic.admit

end tactic

/-
The propositional fields of `category` are annotated with the auto_param `obviously`,
which is defined here as a
[`replacer` tactic](https://leanprover-community.github.io/mathlib_docs/commands.html#def_replacer).
We then immediately set up `obviously` to call `tidy`. Later, this can be replaced with more
powerful tactics.

(In fact, at present this mechanism is not actually used, and the implementation of
`obviously` below stays in place throughout mathlib.)
-/
def_replacer obviously

/--
The default implementation of `obviously`
discharges any goals which contain `sorry` in their type using `sorry`,
and then calls `tidy`.
-/
@[obviously] meta def obviously' :=
tactic.sorry_if_contains_sorry <|>
tactic.tidy <|>
tactic.fail (
"`obviously` failed to solve a subgoal.\n" ++
"You may need to explicitly provide a proof of the corresponding structure field.")
