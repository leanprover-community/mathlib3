/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import group_theory.group_action.basic
import .set

/-!

# stabilizer of complement

We prove `stabilizer_compl` : the stabilizer of the complement is the stabilizer of the set.

## TODO

Put in group_theory.group_action.basic ?

-/

namespace mul_action

open_locale pointwise

variables (G : Type*) [group G] {X : Type*} [mul_action G X]

/-- The stabilizer of the complement is the stabilizer of the set. -/
@[simp] lemma stabilizer_compl {s : set X} : stabilizer G sᶜ = stabilizer G s :=
begin
  have : ∀ (s : set X), stabilizer G s ≤ stabilizer G sᶜ,
  { intros s g h,
    rw [mem_stabilizer_iff, set.smul_compl_set, mem_stabilizer_iff.1 h] },
  refine le_antisymm _ (this _),
  convert this _,
  exact (compl_compl _).symm,
end

end mul_action
