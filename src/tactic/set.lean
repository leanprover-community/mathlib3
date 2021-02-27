/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import tactic.interactive
import tactic.ext
import tactic.tauto
import data.set.default
import data.finset.default


/-! tactics for proving results about sets. Also work with finsets.

set_taut proves set equality using intuitionistic logic.
set_taut' proves set equality using classical logic.

TODO: subset_taut: prove s ⊆ t.
TODO: disjoint_taut: prove two sets are disjoint.
TODO: unify all taut tactics into a single set tactic.
TODO: set_simp: simplify sets. -/


/-- tactic.tautology cannot deduce P b from (∀ b, P b ∧ Q b),
  but it can from (∀ b, P b) ∧ (∀ b, Q b). -/
lemma forall_and_iff_forall_and_forall {β} {P Q : β → Prop} :
  (∀ b, P b ∧ Q b) ↔ (∀ b, P b) ∧ ∀ b, Q b :=
iff.intro 
  (λ h1 : (∀ b, P b ∧ Q b), and.intro (λ b, (h1 b).left) (λ b, (h1 b).right)) 
  (λ h1 : (∀ b, P b) ∧ (∀ b, Q b), (λ b, and.intro (h1.left b) (h1.right b))) 

/-- Helper for set_taut and set_taut'. -/
meta def set_tauth (classical_op:bool) : tactic unit :=
do tactic.ext1 [],
do lemmas ← simp_lemmas.mk_default,
do lemmas' ← simp_lemmas.add_simp lemmas `forall_and_iff_forall_and_forall,
do tactic.simp_all lemmas' [],
do tactic.tautology  {classical := classical_op}

/-- Prove tautological equality of two sets, using intuitionistic logic. -/
meta def set_taut : tactic unit := set_tauth ff

/-- Prove tautological equality of two sets, using classical logic. -/
meta def set_taut' : tactic unit := set_tauth tt

