/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Kexing Ying
-/
import data.set.intervals.ord_connected
import measure_theory.covering.differentiation
import measure_theory.measure.lebesgue
import measure_theory.covering.besicovitch_vector_space
import order.upper_lower

/-!
# Order-connected sets are null-measurable

This file proves that order-connected sets in `ℝⁿ` under the pointwise order are measurable.

## Main declarations

* `is_upper_set.null_frontier`/`is_lower_set.null_frontier`
-/

section
variables {α : Type*} {r r' : α → α → Prop}

lemma directed_on.mono' {s : set α} (hs : directed_on r s)
  (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) :
  directed_on r' s :=
λ x hx y hy, let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy in ⟨z, hz, h hx hz hxz, h hy hz hyz⟩

end

section
variables {α β : Type*} [semilattice_sup α] [preorder β] {f : α → β} {s : set α}

lemma monotone_on.directed_ge (hf : monotone_on f s) : directed_on (≥) f := directed_of_inf hf

end

section
variables {α β : Type*} [preorder α] {f : α → β}

open set

/-- An antitone function on an inf-semilattice is directed. -/
lemma directed_on_of_inf {r : β → β → Prop} {s : set α} (hs : directed_on (≤) s)
  (hf : ∀ ⦃a₁⦄, a₁ ∈ s → ∀ ⦃a₂⦄, a₂ ∈ s → a₁ ≤ a₂ → r (f a₁) (f a₂)) : directed_on r (f '' s) :=
directed_on_image.2 $ hs.mono' hf

variables [preorder β]

lemma monotone.directed_ge (hf : monotone f) : directed (≥) f := directed_of_inf hf

lemma monotone_on.directed_on_ge (hf : monotone_on f s) : directed_on (≥) s f := directed_of_inf hf

end

section
variables {α β : Type*} [semilattice_sup α] [preorder β] {f : α → β} {s : set α}

lemma monotone_on.directed_ge (hf : monotone_on f s) : directed_on (≥) f := directed_of_inf hf

end

section
variables {α β : Type*} [semilattice_inf α] [preorder β] {f : α → β} {s : set α}

lemma monotone.directed_ge (hf : monotone f) : directed (≥) f := directed_of_inf hf

lemma monotone_on.directed_on_ge (hf : monotone_on f s) : directed_on (≥) s f := directed_of_inf hf

end

namespace emetric
variables {α β : Type*} [pseudo_emetric_space α] [pseudo_emetric_space β] {f : α → β} {s t : set α}
  {x : α}

open filter set
open_locale topological_space ennreal

lemma nhds_within_basis_ball : (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, ball x ε ∩ s) :=
nhds_within_has_basis nhds_basis_eball s

lemma nhds_within_basis_closed_ball :
  (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, closed_ball x ε ∩ s) :=
nhds_within_has_basis nhds_basis_closed_eball s

lemma mem_nhds_within_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
nhds_within_basis_ball.mem_iff

lemma tendsto_nhds_within_nhds_within {t : set β} {a b} :
  tendsto f (𝓝[s] a) (𝓝[t] b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
(nhds_within_basis_ball.tendsto_iff nhds_within_basis_ball).trans $
  forall₂_congr $ λ ε hε, exists₂_congr $ λ δ hδ,
  forall_congr $ λ x, by simp; itauto

lemma tendsto_nhds_within_nhds {a b} :
  tendsto f (𝓝[s] a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → edist x a < δ → edist (f x) b < ε :=
by { rw [← nhds_within_univ b, tendsto_nhds_within_nhds_within], simp only [mem_univ, true_and] }

lemma tendsto_nhds_nhds {a b} :
  tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
nhds_basis_eball.tendsto_iff nhds_basis_eball

end emetric

namespace ennreal
open_locale ennreal
variables {s : set ℝ≥0∞} {x : ℝ≥0∞}

open filter set
open_locale topological_space ennreal

lemma nhds_basis_Icc (hx : x ≠ ⊤) :
  (𝓝 x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, Icc (x - ε) (x + ε)) :=
begin
  rw nhds_of_ne_top hx,
  refine has_basis_binfi_principal _ ⟨∞, with_top.coe_lt_top _⟩,

end

lemma nhds_within_basis_ball : (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, Icc x ε ∩ s) :=
nhds_within_has_basis nhds_basis_Icc s

lemma nhds_within_basis_closed_ball :
  (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, closed_ball x ε ∩ s) :=
nhds_within_has_basis nhds_basis_closed_eball s

lemma mem_nhds_within_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
nhds_within_basis_ball.mem_iff

lemma tendsto_nhds_within_nhds_within {t : set β} {a b} :
  tendsto f (𝓝[s] a) (𝓝[t] b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
(nhds_within_basis_ball.tendsto_iff nhds_within_basis_ball).trans $
  forall₂_congr $ λ ε hε, exists₂_congr $ λ δ hδ,
  forall_congr $ λ x, by simp; itauto

lemma tendsto_nhds_within_nhds {a b} :
  tendsto f (𝓝[s] a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → edist x a < δ → edist (f x) b < ε :=
by { rw [← nhds_within_univ b, tendsto_nhds_within_nhds_within], simp only [mem_univ, true_and] }

lemma tendsto_nhds_nhds {a b} :
  tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
nhds_basis_eball.tendsto_iff nhds_basis_eball



end ennreal

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
variables {β : Type*} {π : β → Type*} [nonempty β] [fintype β] [Π b, seminormed_add_comm_group (π b)]
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
variables {ι E : Type*} [fintype ι] [seminormed_add_comm_group E]

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
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 (frontier_subset_closure hx) _ (half_pos hδ),
  refine λ z hz, hs (λ i, _) hy,
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  refine (sub_le_iff_le_add.1 hxy.2).trans ((_root_.sub_le.1 hz.1).trans_eq' _),
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
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 (frontier_subset_closure hx) _ (half_pos hδ),
  refine λ z hz, hs (λ i, _) hy,
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  refine (sub_le_iff_le_add.1 hz.2).trans ((_root_.sub_le.1 hxy.1).trans_eq' _),
  ring,
end

open filter
open_locale topological_space

lemma is_upper_set.null_frontier (hs : is_upper_set s) : volume (frontier s) = 0 :=
begin
  refine eq_bot_mono (volume.mono _)
    (besicovitch.ae_tendsto_measure_inter_div_of_measurable_set _ is_closed_closure.measurable_set),
  exact s,
  refine λ x hx h, _,
  dsimp at h,

  rw emetric.nhds_within_basis_closed_ball.tendsto_iff emetric.nhds_basis_closed_eball at h,
  rw [nhds_within, tendsto_inf_left] at h,
  rw emetric.nhds_basis_eball.tendsto_left_iff at h,
  have := emetric.tendsto_nhds.1 h,
  have := emetric.tendsto_nhds_within_nhds.1 _,
  rotate 9,
  convert h,
  rotate 2,
  apply_instance,
  refl,
  sorry,sorry,
  sorry,sorry,
end

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
