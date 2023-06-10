/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed.order.basic
import analysis.asymptotics.asymptotics

/-!
# A collection of specific asymptotic results

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developped in `analysis.asymptotics.asymptotics`.
-/

open filter asymptotics
open_locale topology

section normed_field

/-- If `f : 𝕜 → E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x - a)⁻¹)` as
`x → a`, `x ≠ a`. -/
lemma filter.is_bounded_under.is_o_sub_self_inv {𝕜 E : Type*} [normed_field 𝕜] [has_norm E]
  {a : 𝕜} {f : 𝕜 → E} (h : is_bounded_under (≤) (𝓝[≠] a) (norm ∘ f)) :
  f =o[𝓝[≠] a] (λ x, (x - a)⁻¹) :=
begin
  refine (h.is_O_const (one_ne_zero' ℝ)).trans_is_o (is_o_const_left.2 $ or.inr _),
  simp only [(∘), norm_inv],
  exact (tendsto_norm_sub_self_punctured_nhds a).inv_tendsto_zero
end

end normed_field

section linear_ordered_field

variables {𝕜 : Type*} [linear_ordered_field 𝕜]

lemma pow_div_pow_eventually_eq_at_top {p q : ℕ} :
  (λ x : 𝕜, x^p / x^q) =ᶠ[at_top] (λ x, x^((p : ℤ) -q)) :=
begin
  apply ((eventually_gt_at_top (0 : 𝕜)).mono (λ x hx, _)),
  simp [zpow_sub₀ hx.ne'],
end

lemma pow_div_pow_eventually_eq_at_bot {p q : ℕ} :
  (λ x : 𝕜, x^p / x^q) =ᶠ[at_bot] (λ x, x^((p : ℤ) -q)) :=
begin
  apply ((eventually_lt_at_bot (0 : 𝕜)).mono (λ x hx, _)),
  simp [zpow_sub₀ hx.ne],
end

lemma tendsto_zpow_at_top_at_top {n : ℤ}
  (hn : 0 < n) : tendsto (λ x : 𝕜, x^n) at_top at_top :=
begin
  lift n to ℕ using hn.le,
  simp only [zpow_coe_nat],
  exact tendsto_pow_at_top (nat.cast_pos.mp hn).ne'
end

lemma tendsto_pow_div_pow_at_top_at_top {p q : ℕ}
  (hpq : q < p) : tendsto (λ x : 𝕜, x^p / x^q) at_top at_top :=
begin
  rw tendsto_congr' pow_div_pow_eventually_eq_at_top,
  apply tendsto_zpow_at_top_at_top,
  linarith
end

lemma tendsto_pow_div_pow_at_top_zero [topological_space 𝕜] [order_topology 𝕜] {p q : ℕ}
  (hpq : p < q) : tendsto (λ x : 𝕜, x^p / x^q) at_top (𝓝 0) :=
begin
  rw tendsto_congr' pow_div_pow_eventually_eq_at_top,
  apply tendsto_zpow_at_top_zero,
  linarith
end

end linear_ordered_field

section normed_linear_ordered_field

variables {𝕜 : Type*} [normed_linear_ordered_field 𝕜]

lemma asymptotics.is_o_pow_pow_at_top_of_lt
  [order_topology 𝕜] {p q : ℕ} (hpq : p < q) :
  (λ x : 𝕜, x^p) =o[at_top] (λ x, x^q) :=
begin
  refine (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_zero hpq),
  exact (eventually_gt_at_top 0).mono (λ x hx hxq, (pow_ne_zero q hx.ne' hxq).elim),
end

lemma asymptotics.is_O.trans_tendsto_norm_at_top {α : Type*} {u v : α → 𝕜} {l : filter α}
  (huv : u =O[l] v) (hu : tendsto (λ x, ‖u x‖) l at_top) : tendsto (λ x, ‖v x‖) l at_top :=
begin
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩,
  rw is_O_with at hcuv,
  convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu),
  ext x,
  rw mul_div_cancel_left _ hc.ne.symm,
end

end normed_linear_ordered_field

section real

open_locale big_operators
open finset

lemma asymptotics.is_o.sum_range {α : Type*} [normed_add_comm_group α]
  {f : ℕ → α} {g : ℕ → ℝ} (h : f =o[at_top] g)
  (hg : 0 ≤ g) (h'g : tendsto (λ n, ∑ i in range n, g i) at_top at_top) :
  (λ n, ∑ i in range n, f i) =o[at_top] (λ n, ∑ i in range n, g i) :=
begin
  have A : ∀ i, ‖g i‖ = g i := λ i, real.norm_of_nonneg (hg i),
  have B : ∀ n, ‖∑ i in range n, g i‖ = ∑ i in range n, g i,
    from λ n, by rwa [real.norm_eq_abs, abs_sum_of_nonneg'],
  apply is_o_iff.2 (λ ε εpos, _),
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), ∀ (b : ℕ), N ≤ b → ‖f b‖ ≤ ε / 2 * g b,
    by simpa only [A, eventually_at_top] using is_o_iff.mp h (half_pos εpos),
  have : (λ (n : ℕ), ∑ i in range N, f i) =o[at_top] (λ (n : ℕ), ∑ i in range n, g i),
  { apply is_o_const_left.2,
    exact or.inr (h'g.congr (λ n, (B n).symm)) },
  filter_upwards [is_o_iff.1 this (half_pos εpos), Ici_mem_at_top N] with n hn Nn,
  calc ‖∑ i in range n, f i‖
  = ‖∑ i in range N, f i + ∑ i in Ico N n, f i‖ :
    by rw sum_range_add_sum_Ico _ Nn
  ... ≤ ‖∑ i in range N, f i‖ + ‖∑ i in Ico N n, f i‖ :
    norm_add_le _ _
  ... ≤ ‖∑ i in range N, f i‖ + ∑ i in Ico N n, (ε / 2) * g i :
    add_le_add le_rfl (norm_sum_le_of_le _ (λ i hi, hN _ (mem_Ico.1 hi).1))
  ... ≤ ‖∑ i in range N, f i‖ + ∑ i in range n, (ε / 2) * g i :
    begin
      refine add_le_add le_rfl _,
      apply sum_le_sum_of_subset_of_nonneg,
      { rw range_eq_Ico,
        exact Ico_subset_Ico (zero_le _) le_rfl },
      { assume i hi hident,
        exact mul_nonneg (half_pos εpos).le (hg i) }
    end
  ... ≤ (ε / 2) * ‖∑ i in range n, g i‖ + (ε / 2) * (∑ i in range n, g i) :
    begin
      rw ← mul_sum,
      exact add_le_add hn (mul_le_mul_of_nonneg_left le_rfl (half_pos εpos).le),
    end
  ... = ε * ‖(∑ i in range n, g i)‖ : by { simp [B], ring }
end

lemma asymptotics.is_o_sum_range_of_tendsto_zero {α : Type*} [normed_add_comm_group α]
  {f : ℕ → α} (h : tendsto f at_top (𝓝 0)) :
  (λ n, ∑ i in range n, f i) =o[at_top] (λ n, (n : ℝ)) :=
begin
  have := ((is_o_one_iff ℝ).2 h).sum_range (λ i, zero_le_one),
  simp only [sum_const, card_range, nat.smul_one_eq_coe] at this,
  exact this tendsto_coe_nat_at_top_at_top
end

/-- The Cesaro average of a converging sequence converges to the same limit. -/
lemma filter.tendsto.cesaro_smul {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {u : ℕ → E} {l : E} (h : tendsto u at_top (𝓝 l)) :
  tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) • (∑ i in range n, u i)) at_top (𝓝 l) :=
begin
  rw [← tendsto_sub_nhds_zero_iff, ← is_o_one_iff ℝ],
  have := asymptotics.is_o_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h),
  apply ((is_O_refl (λ (n : ℕ), (n : ℝ) ⁻¹) at_top).smul_is_o this).congr' _ _,
  { filter_upwards [Ici_mem_at_top 1] with n npos,
    have nposℝ : (0 : ℝ) < n := nat.cast_pos.2 npos,
    simp only [smul_sub, sum_sub_distrib, sum_const, card_range, sub_right_inj],
    rw [nsmul_eq_smul_cast ℝ, smul_smul, inv_mul_cancel nposℝ.ne', one_smul] },
  { filter_upwards [Ici_mem_at_top 1] with n npos,
    have nposℝ : (0 : ℝ) < n := nat.cast_pos.2 npos,
    rw [algebra.id.smul_eq_mul, inv_mul_cancel nposℝ.ne'] }
end

/-- The Cesaro average of a converging sequence converges to the same limit. -/
lemma filter.tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : tendsto u at_top (𝓝 l)) :
  tendsto (λ (n : ℕ), (n ⁻¹ : ℝ) * (∑ i in range n, u i)) at_top (𝓝 l) :=
h.cesaro_smul

end real
