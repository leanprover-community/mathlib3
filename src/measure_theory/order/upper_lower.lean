/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Kexing Ying
-/
import data.set.intervals.ord_connected
import measure_theory.measure.lebesgue
import order.upper_lower

/-!
# Order-connected sets are null-measurable

This file proves that order-connected sets in `ℝⁿ` under the pointwise order are measurable.

## Main declarations

* `is_upper_set.null_frontier`/`is_lower_set.null_frontier`
-/

-- Will come from #14785
section
variables {α : Type*} [preorder α] {s : set α}

def upper_closure : set α → upper_set α := sorry
def lower_closure : set α → lower_set α := sorry

namespace set

lemma ord_connected.upper_closure_inter_lower_closure (h : s.ord_connected) :
  ↑(upper_closure s) ∩ ↑(lower_closure s) = s := sorry

end set

end

open function measure_theory measure_theory.measure metric set

variables {ι : Type*} [fintype ι] {s : set (ι → ℝ)} {x : ι → ℝ} {δ : ℝ}

lemma is_upper_set.exists_subset_ball (hs : is_upper_set s) (hx : x ∈ frontier s) (hδ : 0 < δ) :
  ∃ y ε, 0 < ε ∧ closed_ball y ε ⊆ closed_ball x δ ∧ closed_ball y ε ⊆ s :=
begin
  casesI is_empty_or_nonempty ι,
  { refine ⟨_, _, hδ, subset.rfl, λ y hy, _⟩,
    obtain ⟨z, hz⟩ := (nonempty_frontier_iff.1 ⟨x, hx⟩).1,
    rwa subsingleton.elim y z },
  refine ⟨x + const _ (δ/2), δ/2, half_pos hδ, closed_ball_subset_closed_ball' _, _⟩,
  { simp [abs_of_nonneg hδ.le] },
  { rintro y hy,
    sorry -- This is false
  }
end

lemma is_upper_set.null_frontier (hs : is_upper_set s) : volume (frontier s) = 0 := sorry
lemma is_lower_set.null_frontier (hs : is_lower_set s) : volume (frontier s) = 0 := sorry

lemma set.ord_connected.null_frontier (hs : s.ord_connected) : volume (frontier s) = 0 :=
begin
  rw ← hs.upper_closure_inter_lower_closure,
  refine le_bot_iff.1 ((volume.mono $ (frontier_inter_subset _ _).trans $ union_subset_union
    (inter_subset_left _ _) $ inter_subset_right _ _).trans $ (measure_union_le _ _).trans_eq _),
  rw [(upper_set.upper _).null_frontier, (lower_set.lower _).null_frontier, zero_add, bot_eq_zero],
end

lemma set.ord_connected.null_measurable_set (hs : s.ord_connected) : null_measurable_set s :=
null_measurable_set_of_null_frontier hs.null_frontier
