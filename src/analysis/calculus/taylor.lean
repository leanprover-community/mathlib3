/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.iterated_deriv
import analysis.calculus.mean_value
import measure_theory.integral.interval_integral
import data.polynomial.basic

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → ℝ`
and proves Taylor's theorem, which states that if `f` is suffiently smooth
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylor_coeff_within`: the Taylor coefficient using `deriv_within`
* `taylor_within`: the Taylor polynomial using `deriv_within`

## Main statements

* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder

## TODO

* the Peano form of the remainder
* the integral form of the remainder
* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/


open_locale big_operators interval topological_space

variables {𝕜 E F : Type*}

/-- The `k`th coefficient of the Taylor polynomial. -/
noncomputable
def taylor_coeff (f : ℝ → ℝ) (k : ℕ) (s : set ℝ) (x₀ : ℝ) : ℝ :=
(iterated_deriv_within k f s x₀) / k.factorial

/-- The Taylor polynomial. -/
noncomputable
def taylor_polynomial (f : ℝ → ℝ) (n : ℕ) (s : set ℝ) (x₀ : ℝ) : polynomial ℝ :=
(finset.range (n+1)).sum (λ k, (polynomial.monomial k (taylor_coeff f k s x₀)).comp
  (polynomial.X - polynomial.C x₀))

lemma taylor_polynomial_succ {f : ℝ → ℝ} {n : ℕ} {s : set ℝ} {x₀ : ℝ} :
  taylor_polynomial f (n+1) s x₀ = taylor_polynomial f n s x₀
  + (polynomial.monomial (n+1) (taylor_coeff f (n+1) s x₀)).comp (polynomial.X - polynomial.C x₀) :=
begin
  dunfold taylor_polynomial,
  rw finset.sum_range_succ,
end

/-- The evaluation of the Taylor polynomial. -/
noncomputable
def taylor_sum (f : ℝ → ℝ) (n : ℕ) (s : set ℝ) (x₀ x : ℝ) : ℝ :=
(taylor_polynomial f n s x₀).eval x

lemma div_mul_comm' (a b : ℝ) {c : ℝ} (hc : c ≠ 0) : a / c * b = a * b / c :=
by rw [eq_div_iff hc, mul_assoc, mul_comm b c, ←mul_assoc, div_mul_cancel a hc]

@[simp] lemma taylor_sum_succ {f : ℝ → ℝ} {n : ℕ} {s : set ℝ} {x₀ x : ℝ} :
  taylor_sum f (n+1) s x₀ x = taylor_sum f n s x₀ x
    + iterated_deriv_within (n + 1) f s x₀
    * (x - x₀) ^ (n + 1) / ((↑n + 1) * ↑(n.factorial)) :=
begin
  dunfold taylor_sum,
  rw [taylor_polynomial_succ, polynomial.eval_add],
  simp only [add_right_inj, taylor_coeff, polynomial.eval_comp, polynomial.eval_monomial,
    nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one, polynomial.eval_sub,
    polynomial.eval_X, polynomial.eval_C],
  refine div_mul_comm' _ _ _,
  refine mul_ne_zero (nat.cast_add_one_ne_zero n) _,
  rw nat.cast_ne_zero,
  exact nat.factorial_ne_zero n,
end

/-- The Taylor polynomial of order zero evaluates to `f x`. -/
@[simp] lemma taylor_sum_zero {f : ℝ → ℝ} {s : set ℝ} {x₀ x : ℝ} :
  taylor_sum f 0 s x₀ x = f x₀ :=
begin
  dunfold taylor_sum,
  dunfold taylor_polynomial,
  dunfold taylor_coeff,
  simp,
end

/-- Evaluating the Taylor polynomial at `x = x₀` yields `f x`. -/
@[simp] lemma taylor_sum_self {f : ℝ → ℝ} {n : ℕ} {s : set ℝ} {x₀ : ℝ} :
  taylor_sum f n s x₀ x₀ = f x₀ :=
begin
  induction n with k hk,
  { exact taylor_sum_zero },
  simp [hk]
end

lemma taylor_polynomial_apply {f : ℝ → ℝ} {n : ℕ} {s : set ℝ} {x₀ x : ℝ} : taylor_sum f n s x₀ x =
  ∑ k in finset.range (n+1), (iterated_deriv_within k f s x₀)
    * (x - x₀)^k / k.factorial :=
begin
  induction n with k hk,
  { simp },
  rw [taylor_sum_succ, finset.sum_range_succ, hk],
  simp,
end

/-- If `f` is `n` times continuous differentiable, then the Taylor polynomial is continuous in the
  second variable. -/
lemma taylor_sum_continuous_on {f : ℝ → ℝ} {x₀ x : ℝ} {n : ℕ} (hx : x₀ < x)
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x)) :
  continuous_on (λ t, taylor_sum f n (set.Icc x₀ x) t x) (set.Icc x₀ x) :=
begin
  simp_rw taylor_polynomial_apply,
  refine continuous_on_finset_sum (finset.range (n+1)) (λ i hi, _),
  refine (continuous_on.mul _ ((continuous_on_const.sub continuous_on_id).pow _)).mul
    continuous_on_const,
  rw cont_diff_on_iff_continuous_on_differentiable_on_deriv (unique_diff_on_Icc hx) at hf,
  cases hf,
  specialize hf_left i,
  simp only [finset.mem_range] at hi,
  refine (hf_left _),
  simp only [with_top.coe_le_coe],
  exact nat.lt_succ_iff.mp hi,
end

lemma monomial_has_deriv (t x : ℝ) {n : ℕ} :
  has_deriv_at (λ y, (x - y)^(n+1)) ((-(n+1) * (x - t)^n)) t :=
begin
  simp_rw sub_eq_neg_add,
  rw [←neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ←mul_assoc],
  convert @has_deriv_at.pow _ _ _ _ _ (n+1) ((has_deriv_at_id t).neg.add_const x),
  simp only [nat.cast_add, nat.cast_one],
end

theorem cont_diff_on.of_succ [nondiscrete_normed_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : ℕ}
  (hs : unique_diff_on 𝕜 s) (h : cont_diff_on 𝕜 (↑n + 1) f s) :
  cont_diff_on 𝕜 ↑n f s :=
begin
  rw cont_diff_on_iff_continuous_on_differentiable_on hs at ⊢ h,
  cases h,
  split; intros m hm,
  { refine h_left m (hm.trans _),
    rw [←with_top.coe_one, ←with_top.coe_add, with_top.coe_le_coe, le_add_iff_nonneg_right],
    exact zero_le' },
  refine h_right m (hm.trans _),
  rw [←with_top.coe_one, ←with_top.coe_add, with_top.coe_lt_coe, lt_add_iff_pos_right,
    nat.lt_one_iff],
end

lemma taylor_coeff_has_deriv {f : ℝ → ℝ} {x y : ℝ} {k : ℕ} {s s' : set ℝ}
  (hs : unique_diff_within_at ℝ s y) (hs' : s' ∈ 𝓝 y)
  (hf' : differentiable_on ℝ (iterated_deriv_within (k+1) f s) s') :
  has_deriv_at (λ t, iterated_deriv_within (k+1) f s t
    * (x - t)^(k+1) / ((k+1)* k.factorial))
    (iterated_deriv_within (k+2) f s y * (x - y)^(k+1) / ((k+1)* k.factorial) -
    iterated_deriv_within (k+1) f s y * (x - y)^k / k.factorial) y :=
begin
  have hf'' : has_deriv_at (λ t, iterated_deriv_within (k+1) f s t)
    (iterated_deriv_within (k+2) f s y) y :=
  begin
    convert hf'.has_deriv_at hs',
    rw @iterated_deriv_within_succ _ _ _ _ _ (k.succ) _ _ _ hs,
    exact (hf'.differentiable_at hs').deriv_within hs,
  end,
  convert (hf''.mul (monomial_has_deriv y x)).div_const ((k+1)* k.factorial),
  rw [sub_eq_neg_add, add_comm, add_div, add_right_inj, ←neg_one_mul, ←neg_one_mul (↑k+1 : ℝ)],
  rw [mul_assoc, mul_comm (↑k+1 : ℝ) ((x - y) ^ k), mul_comm (↑k+1 : ℝ), ←mul_assoc, ←mul_assoc],
  rw mul_div_mul_right,
  { simp[neg_div] },
  exact nat.cast_add_one_ne_zero k,
end

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`. -/
lemma taylor_sum_has_deriv {f : ℝ → ℝ} {x x₀ t : ℝ} {n : ℕ}
  (hx : x₀ < x) (ht : t ∈ set.Ioo x₀ x)
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x)) (set.Ioo x₀ x)) :
  has_deriv_at (λ t', taylor_sum f n (set.Icc x₀ x) t' x)
    ((iterated_deriv_within (n+1) f (set.Icc x₀ x) t) * (x - t)^n /n.factorial) t :=
begin
  have ht' := is_open.mem_nhds is_open_Ioo ht,
  have unique_Icc := ((unique_diff_within_at_Ioo ht).mono set.Ioo_subset_Icc_self),
  induction n with k hk,
  { simp only [taylor_sum_zero, iterated_deriv_one, pow_zero, mul_one, nat.factorial_zero,
      nat.cast_one, div_one, has_deriv_at_deriv_iff, zero_add],
    simp only [iterated_deriv_within_zero] at hf',
    rw iterated_deriv_within_one (unique_diff_on_Icc hx)
      (set.mem_of_subset_of_mem set.Ioo_subset_Icc_self ht),
    rw (hf'.differentiable_at ht').deriv_within unique_Icc,
    exact (hf'.differentiable_at ht').has_deriv_at },
  simp_rw [nat.add_succ, taylor_sum_succ],
  simp only [add_zero, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one],
  have hdiff : differentiable_on ℝ (iterated_deriv_within k f (set.Icc x₀ x)) (set.Ioo x₀ x) :=
  begin
    have coe_lt_succ : (↑k : with_top ℕ) < k.succ :=
    by { rw [with_top.coe_lt_coe], exact lt_add_one k },
    refine differentiable_on.mono _ set.Ioo_subset_Icc_self,
    exact hf.differentiable_on_iterated_deriv_within coe_lt_succ (unique_diff_on_Icc hx),
  end,
  specialize hk (cont_diff_on.of_succ (unique_diff_on_Icc hx) hf) hdiff,
  convert hk.add (taylor_coeff_has_deriv unique_Icc ht' hf'),
  exact (add_sub_cancel'_right _ _).symm,
end

/-- **Taylor's theorem** with the general mean value form of the remainder. -/
lemma taylor_mean_remainder {f g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x)) (set.Ioo x₀ x))
  (hx : x₀ < x)
  (gcont : continuous_on g (set.Icc x₀ x))
  (gdiff : ∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at g (g' x_1) x_1)
  (g'_ne : ∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → g' x_1 ≠ 0) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - taylor_sum f n (set.Icc x₀ x) x₀ x =
  (iterated_deriv_within (n+1) f (set.Icc x₀ x) x') * (x - x')^n /n.factorial * (g x - g x₀) / g' x'
  :=
begin
  rcases exists_ratio_has_deriv_at_eq_ratio_slope (λ t, taylor_sum f n (set.Icc x₀ x) t x)
    (λ t, (iterated_deriv_within (n+1) f (set.Icc x₀ x) t) * (x - t)^n /n.factorial) hx
    (taylor_sum_continuous_on hx hf) (λ _ hy, taylor_sum_has_deriv hx hy hf hf')
    g g' gcont gdiff with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [taylor_sum_self] at h,
  rw [mul_comm, ←div_left_inj' (g'_ne y hy), mul_div_cancel _ (g'_ne y hy)] at h,
  exact h.symm,
end

/-- **Taylor's theorem** with the Lagrange form of the remainder. -/
lemma taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x)) (set.Ioo x₀ x))
  (hx : x₀ < x) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - taylor_sum f n (set.Icc x₀ x) x₀ x =
  (iterated_deriv_within (n+1) f (set.Icc x₀ x) x') * (x - x₀)^(n+1) /(n+1).factorial :=
begin
  have gcont : continuous_on (λ (t : ℝ), (x - t) ^ (n + 1)) (set.Icc x₀ x) :=
  by { refine continuous.continuous_on _, continuity },
  have xy_ne : ∀ (y : ℝ), y ∈ set.Ioo x₀ x → (x - y)^n ≠ 0 :=
  begin
    intros y hy,
    refine pow_ne_zero _ _,
    rw [set.mem_Ioo] at hy,
    rw sub_ne_zero,
    exact hy.2.ne.symm,
  end,
  have hg' : ∀ (y : ℝ), y ∈ set.Ioo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 :=
  λ y hy, mul_ne_zero (neg_ne_zero.mpr (nat.cast_add_one_ne_zero n)) (xy_ne y hy),
  rcases taylor_mean_remainder hf hf' hx gcont (λ y _, monomial_has_deriv y x) hg' with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [sub_self, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h,
  rw [h, neg_div, ←div_neg, neg_mul, neg_neg],
  field_simp,
  rw [mul_assoc, mul_comm ((x - y)^n), ←mul_assoc, ←mul_assoc, mul_comm (↑n+1 : ℝ),
    mul_div_mul_right _ _ (xy_ne y hy)]
end

/-- **Taylor's theorem** with the Cauchy form of the remainder. -/
lemma taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x)) (set.Ioo x₀ x))
  (hx : x₀ < x) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - taylor_sum f n (set.Icc x₀ x) x₀ x =
  (iterated_deriv_within (n+1) f (set.Icc x₀ x) x') * (x - x')^n /n.factorial * (x - x₀) :=
begin
  have gcont : continuous_on id (set.Icc x₀ x) :=
  by { refine continuous.continuous_on _, continuity },
  have gdiff : (∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at id
    ((λ (t : ℝ), (1 : ℝ)) x_1) x_1) := λ _ _, has_deriv_at_id _,
  rcases taylor_mean_remainder hf hf' hx gcont gdiff (λ _ _, by simp) with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [id.def, div_one] at h,
  exact h,
end
