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

section
variables {ι α : Type*} [fintype ι] [pseudo_emetric_space α]

lemma edist_pi_const_le (a b : α) : edist (λ _ : ι, a) (λ _, b) ≤ edist a b :=
edist_pi_le_iff.2 $ λ _, le_rfl

end

section
variables {ι α : Type*} [fintype ι] [pseudo_metric_space α]

lemma dist_pi_const_le (a b : α) : dist (λ _ : ι, a) (λ _, b) ≤ dist a b :=
(dist_pi_le_iff dist_nonneg).2 $ λ _, le_rfl

lemma nndist_pi_const_le (a b : α) : nndist (λ _ : ι, a) (λ _, b) ≤ nndist a b :=
nndist_pi_le_iff.2 $ λ _, le_rfl

lemma where_is_that {s : set α} {x : α} {ε : ℝ} (hx : x ∈ frontier s) (hε : 0 < ε) :
  ∃ z ∈ s, dist x z < ε := sorry

end

section
variables {β : Type*} {π : β → Type*} [nonempty β] [fintype β] [Π b, pseudo_metric_space (π b)]
  {f g : Π b, π b} {r : ℝ}

lemma dist_pi_le_iff' : dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r :=
begin
  by_cases hr : 0 ≤ r,
  { exact dist_pi_le_iff hr },
  { exact iff_of_false (λ h, hr $ dist_nonneg.trans h)
      (λ h, hr $ dist_nonneg.trans $ h $ classical.arbitrary _) }
end

end

section
variables {β : Type*} {π : β → Type*} [nonempty β] [fintype β] [Π b, semi_normed_group (π b)]
  {f : Π b, π b} {r : ℝ}

lemma pi_norm_le_iff' : ∥f∥ ≤ r ↔ ∀ b, ∥f b∥ ≤ r :=
begin
  by_cases hr : 0 ≤ r,
  { exact pi_norm_le_iff hr },
  { exact iff_of_false (λ h, hr $ (norm_nonneg _).trans h)
      (λ h, hr $ (norm_nonneg _).trans $ h $ classical.arbitrary _) }
end

end

section
variables {ι E : Type*} [fintype ι] [semi_normed_group E]

lemma pi_norm_const_le (a : E) : ∥(λ _ : ι, a)∥ ≤ ∥a∥ :=
(pi_norm_le_iff $ norm_nonneg _).2 $ λ _, le_rfl

end

open function measure_theory measure_theory.measure metric set

variables {ι : Type*} [fintype ι] {s : set (ι → ℝ)} {x : ι → ℝ} {δ : ℝ}

protected lemma is_upper_set.closure (h : is_upper_set s) : is_upper_set (closure s) := sorry
protected lemma is_lower_set.closure (h : is_lower_set s) : is_lower_set (closure s) := sorry

protected lemma is_upper_set.interior (h : is_upper_set s) : is_upper_set (interior s) :=
by { rw [←is_lower_set_compl, ←closure_compl], exact h.compl.closure }

protected lemma is_lower_set.interior (h : is_lower_set s) : is_lower_set (interior s) :=
by { rw [←is_upper_set_compl, ←closure_compl], exact h.compl.closure }

lemma is_upper_set.exists_subset_ball (hs : is_upper_set s) (hx : x ∈ frontier s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ s :=
begin
  refine ⟨x + const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_add_left,
    refine (add_le_add_left (pi_norm_const_le _) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := where_is_that hx (half_pos hδ),
  refine λ z hz, hs (λ i, _) hy,
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  refine (sub_le_iff_le_add.1 hxy.2).trans ((sub_le.1 hz.1).trans_eq' _),
  ring,
end

lemma is_lower_set.exists_subset_ball (hs : is_lower_set s) (hx : x ∈ frontier s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ s :=
begin
  refine ⟨x - const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_sub_left,
    refine (add_le_add_left (pi_norm_const_le _) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := where_is_that hx (half_pos hδ),
  refine λ z hz, hs (λ i, _) hy,
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  refine (sub_le_iff_le_add.1 hz.2).trans ((sub_le.1 hxy.1).trans_eq' _),
  ring,
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
