/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import group_theory.quotient_group
import algebra.category.Group.abelian
import data.real.basic
import order.filter.at_top_bot
import topology.metric_space.basic
import topology.algebra.ordered.monotone_convergence

/-!
some lemmas that I didn't bother to put in the correct location, or check if
they are somewhere already in mathlib.
-/

open_locale classical pointwise

section

variables (G : Type*) [add_comm_group G]

lemma mem_smul (m : ℕ) {a : G} :
 a ∈ m • (⊤ : add_subgroup G) ↔ ∃ a' : G, a = m • a' :=
begin
  split; intro ha,
  rcases ha with ⟨a', h1, h2⟩,
  use a', rw ←h2, refl,

  obtain ⟨a', h⟩ := ha,
  use a', split, simp only [add_subgroup.coe_top], rw h, refl,
end

section

open filter
open_locale filter

lemma eventually_le_one (K : ℝ) (hk : 0 ≤ K) :
  ∃ (M : ℕ), ∀ (n : ℕ), M ≤ n → ((2 : ℝ)⁻¹)^n * K ≤ 1 :=
have ineq3 : ∀ (n : ℕ), n < 2 ^ n,
begin
  intros n, induction n with n ih, norm_num,
  rw nat.lt_iff_add_one_le at ih,
  apply lt_of_le_of_lt, exact ih,
  apply nat.pow_lt_pow_of_lt_right, norm_num,
  exact lt_add_one n,
end,
have l1 : tendsto (λ (n : ℕ), (2 : ℝ)⁻¹^n) at_top (nhds 0), begin
  rw [tendsto_iff_dist_tendsto_zero],
  simp_rw [real.dist_0_eq_abs],
  apply tendsto_at_top_is_glb,
  intros m n hm, dsimp only, rw [abs_of_nonneg, abs_of_nonneg],
  rw [inv_pow₀, inv_pow₀, inv_le_inv], norm_cast,
  apply nat.pow_le_pow_of_le_right, norm_num, exact hm, apply pow_pos,
  norm_num, apply pow_pos, norm_num, apply pow_nonneg, norm_num, apply pow_nonneg, norm_num,

  split,
  rw mem_lower_bounds, intros x hx, rw set.mem_range at hx,
  obtain ⟨n, rfl⟩ := hx, exact abs_nonneg _,

  rw mem_upper_bounds, intros y hy, rw [mem_lower_bounds] at hy,
  by_contra rid, simp only [not_le] at rid,
  have ineq := archimedean.arch 1 rid,
  obtain ⟨n, hn⟩ := ineq,
  rw [nsmul_eq_mul] at hn,
  suffices : (n : ℝ) * y ≤ n/(2^n),
  have ineq2 := le_trans hn this,
  rw one_le_div at ineq2, norm_cast at ineq2,
  specialize ineq3 n,
  linarith, apply pow_pos, norm_num,
  rw div_eq_mul_inv, apply mul_le_mul, refl, apply hy,
  rw set.mem_range, use n, rw abs_of_nonneg, rw inv_pow₀,
  apply pow_nonneg, norm_num, linarith, norm_cast, exact nat.zero_le _,
end,
begin
  by_cases K = 0, rw h, use 0, intros, rw mul_zero, linarith,
  have ev := @filter.tendsto.eventually ℕ ℝ (λ n, (2 : ℝ)⁻¹^n) at_top (nhds 0)
    (λ r, r * K ≤ 1) l1,
  rw [eventually_iff, eventually_iff] at ev,
  simp only [mem_at_top_sets, ge_iff_le, inv_pow₀, set.mem_set_of_eq] at ev,
  simp_rw inv_pow₀, refine ev _,
  rw mem_nhds_iff,
  use set.Iio (1/K), split,
  intros x hx, rw ←set.Iio_def at hx, simp only [one_div, set.mem_set_of_eq] at hx ⊢,
  rw show (1 : ℝ) = K⁻¹ * K, by rw inv_mul_cancel h,
  apply mul_le_mul, linarith [hx], refl, exact hk, rw inv_nonneg, exact hk,
  split, simp only [one_div], exact is_open_Iio, rw ←set.Iio_def,
  suffices : 0 < 1/K, exact this, apply div_pos, linarith,
  apply lt_of_le_of_ne, exact hk, symmetry, exact h,
end

end

end
