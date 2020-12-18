/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import analysis.real.prelims_polynomial
import topology.algebra.polynomial
import analysis.calculus.mean_value

/-!
This file contains some lemmas about real polynomials and their derivatives
-/

open polynomial real set

/-- This lemma is almost identical to a lemma in the PR:
the last condition of the present lemma is `x ∉ f.roots.to_finset`,
the last condition of the original PR is `f.eval x ≠ 0`.  -/
lemma non_root_small_interval_of_polynomial
  (α : ℝ) (f : polynomial ℝ) (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), x ∉ f.roots.to_finset :=
begin
  obtain ⟨l, m, I, F⟩ := Ioo_not_mem_finset α f.roots.to_finset,
  refine ⟨min 1 (min (1 / M) (min (α - l) (m - α))), _, _, _, λ x K, (λ J, F x (mem_Ioo.mpr _) J)⟩,
  { rw [lt_min_iff, lt_min_iff, lt_min_iff, one_div, inv_pos],
    exact ⟨zero_lt_one, hM, sub_pos.mpr I.1, sub_pos.mpr I.2⟩ },
  { exact (min_le_iff.mpr (or.inr (min_le_iff.mpr (or.inl rfl.le)))) },
  { exact min_le_iff.mpr (or.inl rfl.le) },
  { have H : (x < α + (α - l) ∧ l < x) ∧ x < m ∧ α - x < m - α,
    { simp only [abs_lt, neg_lt_sub_iff_lt_add, lt_min_iff, sub_lt_sub_iff_left,
        add_sub_cancel'_right] at K,
      exact K.2.2 },
    exact ⟨H.1.2, H.2.1⟩ }
end

/-- A polynomial is bounded on a compact interval. In this formulation, there is the
flexibility of using a larger-than-optimal bound. -/
lemma exists_forall_ge_of_polynomial_Ioo (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, ∀ N, M ≤ N → ∀ y ∈ Icc (α - 1) (α + 1), abs (eval y f) ≤ N :=
begin
  obtain ⟨x, ⟨-, hy⟩⟩ := is_compact.exists_forall_ge compact_Icc ⟨α - 1, ⟨rfl.le,
    sub_le_iff_le_add.mpr (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg rfl.le zero_le_one)
    zero_le_one)⟩⟩ (continuous_abs.comp (polynomial.continuous f)).continuous_on,
  exact ⟨abs (f.eval x), λ N hN y hy1, le_trans (hy y hy1) hN⟩,
end

/-- A lemma in the original PR, now a consequence of `exists_forall_ge_of_polynomial_Ioo`. -/
lemma exists_forall_ge_of_polynomial_eval (α : ℝ) (f : polynomial ℝ):
  ∃ M : ℝ, 0 < M ∧ ∀ (y : ℝ), abs (y - α) ≤ 1 → abs (eval y f) ≤ M :=
begin
  obtain ⟨M, F⟩ := exists_forall_ge_of_polynomial_Ioo α f,
  simp_rw ← abs_le_iff_mem_Icc at F,
  by_cases M0 : M ≤ 0,
  { exact ⟨1, zero_lt_one, λ y h, F 1 (le_trans M0 zero_le_one) y h⟩ },
  { exact ⟨M, not_le.mp M0, F M rfl.ge⟩ },
end

/-- Almost the original statement: I moved the introduction of the second real number `x`
next to the introduction of `α`, I introduced the `hax` hypothesis and used a differentiable
function, instead of a polynomial. -/
lemma exists_deriv_eq_slope_of_fun_zero_lt (α x : ℝ) (f : ℝ → ℝ)
  (fc : continuous_on f (Icc α x)) (df : differentiable_on ℝ f (Ioo α x))
  (h_α_root : f α = 0) (h : f x ≠ 0)
   (hax : α < x) :
  ∃ x₀, α - x = - ((f x) / (deriv f x₀)) ∧ deriv f x₀ ≠ 0 ∧ x₀ ∈ Ioo α x:=
begin
  obtain ⟨c, I, F⟩ := exists_deriv_eq_slope f hax fc df,
  rw [h_α_root, sub_zero] at F,
  refine ⟨c, by rwa [F, div_div_cancel', neg_sub], λ d, _, I⟩,
  { rw [eq_comm, d, div_eq_iff (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
    exact h F },
end

/-- The second half of exists_deriv_eq_slope_of_fun_zero_gt. -/
lemma exists_deriv_eq_slope_of_fun_zero_gt (α x : ℝ) (f : ℝ → ℝ)
  (fc : continuous_on f (Icc x α)) (df : differentiable_on ℝ f (Ioo x α))
  (h_α_root : f α = 0) (h : f x ≠ 0) (hax : x < α) :
  ∃ x₀, α - x = - ((f x) / (deriv f x₀)) ∧ (deriv f x₀ ≠ 0) ∧ (x₀ ∈ Ioo x α) :=
begin
  obtain ⟨c, I, F⟩ := exists_deriv_eq_slope f hax fc df,
  rw [h_α_root, zero_sub] at F,
  refine ⟨c, by { rwa [F, ← neg_div, div_div_cancel'], exact neg_ne_zero.mpr h }, λ d, _, I⟩,
  { rw [eq_comm, d, div_eq_iff_mul_eq (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
    exact h (neg_eq_zero.mp F.symm) },
end

/-- The literal statement appearing in the PR. -/
lemma exists_deriv_eq_slope_of_polynomial_root (α : ℝ) (f : polynomial ℝ) (h_α_root : f.eval α = 0)
  (x : ℝ) (h : f.eval x ≠ 0) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  rcases @trichotomous _ (has_lt.lt) _ α x with ax | rfl | xa,
  { obtain ⟨c, d, e, I⟩:= exists_deriv_eq_slope_of_fun_zero_lt α x (λ y, f.eval y)
      (polynomial.continuous_on f) (polynomial.differentiable_on f) h_α_root h ax,
    refine ⟨c, by rwa [polynomial.deriv] at d, by rwa [polynomial.deriv] at e, _⟩,
    exact ⟨abs_lt_abs_left I, abs_lt_abs_right I⟩ },
  { exact false.rec _ (h h_α_root) },
  { obtain ⟨c, d, e, I⟩:= exists_deriv_eq_slope_of_fun_zero_gt α x (λ y, f.eval y)
      (polynomial.continuous_on f) (polynomial.differentiable_on f) h_α_root h xa,
    refine ⟨c, by rwa [polynomial.deriv] at d, by rwa [polynomial.deriv] at e, _⟩,
    { rw abs_sub _ x,
      exact ⟨abs_lt_abs_right I, abs_lt_abs_left I⟩ } },
end
