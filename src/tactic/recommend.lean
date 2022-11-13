/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import tactic.core

/-!
# `recommend`

The `recommend` tactic searches for lemmas in the current environment
that look like they could be useful to prove the current goal.

It is based on premise selection heuristic used in [CoqHammer][czajka2018],
with a preprocessing step that removes type arguments, type class instances, etc.
This heuristic analyzes the proofs of the theorems in the environment:
it will suggest lemmas that have been used in proofs of
similar theorems as the current goal.

The heuristic is completely syntactic;
it won't unfold definitions during the search,
and doesn't know about types and type classes.
-/

namespace tactic

open feature_search

/-- Attribute that marks a theorem to be ignored by the `recommend` tactic. -/
@[user_attribute]
meta def recommend_ignore_attr : user_attribute :=
{ name := `recommend_ignore, descr := "Marks a theorem to be ignored by the `recommend` tactic." }

attribute [recommend_ignore] eq.mpr eq.rec id_tag nat eq
  has_zero.zero has_one.one has_lt.lt has_le.le

/-- Returns true if `rw [const]` succeeds (or `rw [← const]` if `symm` is true). -/
meta def can_rw_with_at_goal (const : name) (symm : bool) : tactic bool :=
retrieve' $ succeeds $ interactive.rw
  { rules := [{ pos := default, symm := symm, rule := expr.const const [] }], end_pos := none }
  (interactive.loc.ns [none])

/--
`recommend` is a tactic to search for existing lemmas in the library
that could be useful to close the current goal.

The `recommend` tactic does not unfold any definitions.
-/
meta def interactive.recommend (max_results := 30) : tactic unit := do
tgt ← retrieve' $ revert_all >> target,
env ← get_env,
let cfg : feature_cfg := {},
let pred := env.mk_predictor {.. cfg},
let fv := feature_vec.of_expr env tgt cfg,
let results := pred.predict fv max_results,
ignored ← attribute.get_instances recommend_ignore_attr.name,
let results := results.filter (λ res, res.1 ∉ ignored),
results.mmap' (λ res : name × native.float, do
  mwhen (retrieve' $ succeeds $ applyc res.1) $ trace!"Try this: apply {res.1}",
  mwhen (can_rw_with_at_goal res.1 ff) $ trace!"Try this: rw {res.1}",
  mwhen (can_rw_with_at_goal res.1 tt) $ trace!"Try this: rw ← {res.1}"),
trace "\nOther useful lemmas:",
results.mmap' (λ res, trace!"{res.1} (score: {res.2})")

add_tactic_doc
{ name        := "recommend",
  category    := doc_category.tactic,
  decl_names  := [``interactive.recommend],
  tags        := ["search", "Try this"] }

end tactic
