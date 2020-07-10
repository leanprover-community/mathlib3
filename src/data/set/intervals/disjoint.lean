/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import data.set.lattice

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into `data.set.intervals.basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `data.set.lattice`, including `disjoint`.
-/

universe u

variables {α : Type u}


namespace set

section decidable_linear_order
variables [decidable_linear_order α] {a₁ a₂ b₁ b₂ : α}

lemma Ico_disjoint_Ico : disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ :=
by simp only [set.disjoint_iff, subset_empty_iff, Ico_inter_Ico, Ico_eq_empty_iff,
  inf_eq_min, sup_eq_max]

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
lemma eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α}
  (h : disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂) (h2 : x₂ ∈ Ico y₁ y₂) :
  y₁ = x₂ :=
begin
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h,
  apply le_antisymm h2.1,
  exact h.elim (λ h, absurd hx (not_lt_of_le h)) id
end

end decidable_linear_order

end set
