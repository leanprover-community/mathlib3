/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import analysis.normed.order.upper_lower
import logic.lemmas
import measure_theory.covering.besicovitch_vector_space

/-!
# Order-connected sets are null-measurable

This file proves that order-connected sets in `ℝⁿ` under the pointwise order are null-measurable.
Recall that `x ≤ y` iff `∀ i, x i ≤ y i`, and `s` is order-connected iff
`∀ x y ∈ s, ∀ z, x ≤ z → z ≤ y → z ∈ s`.

## Main declarations

* `set.ord_connected.null_frontier`: The frontier of an order-connected set in `ℝⁿ` has measure `0`.

## Notes

We prove null-measurability in `ℝⁿ` with the `∞`-metric, but this transfers directly to `ℝⁿ` with
the Euclidean metric because they have the same measurable sets.

Null-measurability can't be strengthened to measurability because any antichain (and in particular
any subset of the antidiagonal `{(x, y) | x + y = 0}`) is order-connected.

## TODO

Generalize so that it also applies to `ℝ × ℝ`, for example.
-/

open filter measure_theory metric set
open_locale topology

variables {ι : Type*} [fintype ι] {s : set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

private lemma aux₀
  (h : ∀ δ, 0 < δ → ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ interior s) :
  ¬ tendsto (λ r, volume (closure s ∩ closed_ball x r) / volume (closed_ball x r)) (𝓝[>] 0)
    (𝓝 0) :=
begin
  choose f hf₀ hf₁ using h,
  intros H,
  obtain ⟨ε, hε, hε', hε₀⟩ := exists_seq_strict_anti_tendsto_nhds_within (0 : ℝ),
  refine not_eventually.2 (frequently_of_forall $ λ _, lt_irrefl $
    ennreal.of_real $ 4⁻¹ ^ fintype.card ι)
   ((tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds _).mono $ λ n, lt_of_le_of_lt _),
  swap,
  refine (ennreal.div_le_div_right (volume.mono $ subset_inter
    ((hf₁ _ $ hε' n).trans interior_subset_closure) $ hf₀ _ $ hε' n) _).trans_eq' _,
  dsimp,
  have := hε' n,
  rw [real.volume_pi_closed_ball, real.volume_pi_closed_ball, ←ennreal.of_real_div_of_pos, ←div_pow,
    mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div],
  all_goals { positivity },
end

private lemma aux₁
  (h : ∀ δ, 0 < δ →
    ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ interior sᶜ) :
  ¬ tendsto (λ r, volume (closure s ∩ closed_ball x r) / volume (closed_ball x r)) (𝓝[>] 0)
    (𝓝 1) :=
begin
  choose f hf₀ hf₁ using h,
  intros H,
  obtain ⟨ε, hε, hε', hε₀⟩ := exists_seq_strict_anti_tendsto_nhds_within (0 : ℝ),
  refine not_eventually.2 (frequently_of_forall $ λ _, lt_irrefl $
    1 - ennreal.of_real (4⁻¹ ^ fintype.card ι))
    ((tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) $
    ennreal.sub_lt_self ennreal.one_ne_top one_ne_zero _).mono $ λ n, lt_of_le_of_lt' _),
  swap,
  refine (ennreal.div_le_div_right (volume.mono _) _).trans_eq _,
  { exact closed_ball x (ε n) \ closed_ball (f (ε n) $ hε' n) (ε n / 4) },
  { rw diff_eq_compl_inter,
    refine inter_subset_inter_left _ _,
    rw [subset_compl_comm, ←interior_compl],
    exact hf₁ _ _ },
  dsimp,
  have := hε' n,
  rw [measure_diff (hf₀ _ _) _ ((real.volume_pi_closed_ball _ _).trans_ne ennreal.of_real_ne_top),
    real.volume_pi_closed_ball, real.volume_pi_closed_ball,  ennreal.sub_div (λ _ _, _),
    ennreal.div_self _ ennreal.of_real_ne_top, ←ennreal.of_real_div_of_pos, ←div_pow,
    mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div],
  all_goals { positivity <|> measurability },
end

lemma is_upper_set.null_frontier (hs : is_upper_set s) : volume (frontier s) = 0 :=
begin
  refine eq_bot_mono (volume.mono $ λ x hx, _)
    (besicovitch.ae_tendsto_measure_inter_div_of_measurable_set _ is_closed_closure.measurable_set),
  { exact s },
  by_cases x ∈ closure s; simp [h],
  { exact aux₁ (λ _, hs.compl.exists_subset_ball $ frontier_subset_closure $
      by rwa frontier_compl) },
  { exact aux₀ (λ _, hs.exists_subset_ball $ frontier_subset_closure hx) }
end

lemma is_lower_set.null_frontier (hs : is_lower_set s) : volume (frontier s) = 0 :=
begin
  refine eq_bot_mono (volume.mono $ λ x hx, _)
    (besicovitch.ae_tendsto_measure_inter_div_of_measurable_set _ is_closed_closure.measurable_set),
  { exact s },
  by_cases x ∈ closure s; simp [h],
  { exact aux₁ (λ _, hs.compl.exists_subset_ball $ frontier_subset_closure $
      by rwa frontier_compl) },
  { exact aux₀ (λ _, hs.exists_subset_ball $ frontier_subset_closure hx) }
end

lemma set.ord_connected.null_frontier (hs : s.ord_connected) : volume (frontier s) = 0 :=
begin
  rw ← hs.upper_closure_inter_lower_closure,
  refine le_bot_iff.1 ((volume.mono $ (frontier_inter_subset _ _).trans $ union_subset_union
    (inter_subset_left _ _) $ inter_subset_right _ _).trans $ (measure_union_le _ _).trans_eq _),
  rw [(upper_set.upper _).null_frontier, (lower_set.lower _).null_frontier, zero_add, bot_eq_zero],
end

protected lemma set.ord_connected.null_measurable_set (hs : s.ord_connected) :
  null_measurable_set s :=
null_measurable_set_of_null_frontier hs.null_frontier

lemma is_antichain.volume_eq_zero [nonempty ι] (hs : is_antichain (≤) s) : volume s = 0 :=
le_bot_iff.1 $ (volume.mono $ by { rw [←closure_diff_interior, hs.interior_eq_empty, diff_empty],
  exact subset_closure }).trans_eq hs.ord_connected.null_frontier
