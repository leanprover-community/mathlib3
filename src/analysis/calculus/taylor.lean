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

## Main definitions

* `taylor_sum`: The Taylor polynomial

## Main statements

* `taylor_mean_remainder`: Taylor's theorem with the Lagrange form of the remainder term

## Tags

Foobars, barfoos
-/


open_locale big_operators interval

variables {f : ℝ → ℝ} {n : ℕ} {x₀ x : ℝ}


/-- The `k`th coefficient of the Taylor polynomial. -/
noncomputable
def taylor_coeff (f : ℝ → ℝ) (k : ℕ) (x₀ : ℝ) : ℝ :=
(iterated_deriv k f x₀) / k.factorial

/-- The Taylor polynomial. -/
noncomputable
def taylor_polynomial (f : ℝ → ℝ) (n : ℕ) (x₀ : ℝ) : polynomial ℝ :=
(finset.range (n+1)).sum (λ k, polynomial.monomial k (taylor_coeff f k x₀))

lemma taylor_polynomial_succ {f : ℝ → ℝ} {n : ℕ} {x₀ : ℝ} :
  taylor_polynomial f (n+1) x₀ = taylor_polynomial f n x₀
    + polynomial.monomial (n+1) (taylor_coeff f (n+1) x₀) :=
begin
  dunfold taylor_polynomial,
  rw finset.sum_range_succ,
end

/-- The Taylor polynomial as a function. -/
noncomputable
def taylor_sum (f : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ) : ℝ :=
polynomial.eval (x - x₀) (taylor_polynomial f n x₀)

lemma div_mul_comm' (a b : ℝ) {c : ℝ} (hc : c ≠ 0) : a / c * b = a * b / c :=
by rw [eq_div_iff hc, mul_assoc, mul_comm b c, ←mul_assoc, div_mul_cancel a hc]

@[simp] lemma taylor_sum_succ {f : ℝ → ℝ} {n : ℕ} {x₀ x : ℝ} :
  taylor_sum f (n+1) x₀ x = taylor_sum f n x₀ x
    + iterated_deriv (n + 1) f x₀ * (x - x₀) ^ (n + 1) / ((↑n + 1) * ↑(n.factorial)) :=
begin
  dunfold taylor_sum,
  rw taylor_polynomial_succ,
  rw polynomial.eval_add,
  simp only [taylor_coeff, polynomial.eval_monomial, add_right_inj],
  simp only [nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one],
  refine div_mul_comm' _ _ _,
  refine mul_ne_zero (nat.cast_add_one_ne_zero n) _,
  rw nat.cast_ne_zero,
  exact nat.factorial_ne_zero n,
end

@[simp] lemma taylor_sum_zero {f : ℝ → ℝ} {x₀ x : ℝ} :
  taylor_sum f 0 x₀ x = f x₀ :=
begin
  dunfold taylor_sum,
  dunfold taylor_polynomial,
  dunfold taylor_coeff,
  simp,
end

@[simp] lemma taylor_sum_self {f : ℝ → ℝ} {n : ℕ} {x : ℝ} :
  taylor_sum f n x x = f x :=
begin
  induction n with k hk,
  { exact taylor_sum_zero },
  simp [hk]
end

lemma taylor_polynomial_apply {f : ℝ → ℝ} {n : ℕ} {x₀ x : ℝ} : taylor_sum f n x₀ x =
  ∑ k in finset.range (n+1), (iterated_deriv k f x₀) * (x - x₀)^k / k.factorial :=
begin
  --dunfold taylor_sum',
  induction n with k hk,
  { simp },
  rw taylor_sum_succ,
  rw finset.sum_range_succ,
  rw hk,
  simp,
end

/-- If `f` is `n` times continuous differentiable, then the Taylor polynomial is continuous in the
  second variable. -/
lemma taylor_sum_continuous {f : ℝ → ℝ} (hf : cont_diff ℝ (n+1) f) {x : ℝ} :
  continuous (λ t, taylor_sum f n t x) :=
begin
  simp_rw taylor_polynomial_apply,
  continuity,
  rw cont_diff_iff_iterated_deriv at hf,
  cases hf,
  simp at H,
  refine hf_left i _,
  rw [←with_top.coe_one, ←with_top.coe_add, with_top.coe_le_coe],
  exact H.le,
end

lemma monomial_has_deriv (t x : ℝ) : has_deriv_at (λ y, (x - y)^(n+1)) ((-(n+1) * (x - t)^n)) t :=
begin
  simp_rw sub_eq_neg_add,
  rw [←neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ←mul_assoc],
  convert @has_deriv_at.pow _ _ _ _ _ (n+1) ((has_deriv_at_id t).neg.add_const x),
  simp only [nat.cast_add, nat.cast_one],
end

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`. -/
lemma taylor_sum_has_deriv {f : ℝ → ℝ} (hf : cont_diff ℝ (n+1) f) {x t : ℝ} :
  has_deriv_at (λ t, taylor_sum f n t x) ((iterated_deriv (n+1) f t) * (x - t)^n /n.factorial) t :=
begin
  induction n with k hk,
  { simp only [taylor_sum_zero, iterated_deriv_one, pow_zero, mul_one, nat.factorial_zero,
      nat.cast_one, div_one, has_deriv_at_deriv_iff],
    refine (hf.differentiable rfl.le).differentiable_at },
  simp_rw nat.add_succ,
  simp_rw taylor_sum_succ,
  simp only [add_zero, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one],
  specialize hk hf.of_succ,
  have hxt : has_deriv_at (λ t, (x - t)^(k+1)) ((-(k+1) * (x - t)^k)) t :=
  begin
    simp_rw sub_eq_neg_add,
    rw [←neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ←mul_assoc],
    convert @has_deriv_at.pow _ _ _ _ _ (k+1) ((has_deriv_at_id t).neg.add_const x),
    simp only [nat.cast_add, nat.cast_one],
  end,
  have hf' : has_deriv_at (λ t, iterated_deriv (k+1) f t) (iterated_deriv (k.succ.succ) f t) t :=
  begin
    rw @iterated_deriv_succ _ _ _ _ _ (k.succ),
    rw cont_diff_iff_iterated_deriv at hf,
    cases hf,
    refine has_deriv_at_deriv_iff.mpr (hf_right (k+1) _ t),
    rw [←with_top.coe_one, ←with_top.coe_add, with_top.coe_lt_coe, lt_add_iff_pos_right,
      nat.lt_one_iff],
  end,
  have : has_deriv_at (λ t, iterated_deriv (k+1) f t * (x - t)^(k+1) / ((k+1)* k.factorial))
    (iterated_deriv (k.succ.succ) f t * (x - t)^(k+1) / ((k+1)* k.factorial) -
    iterated_deriv (k+1) f t * (x - t)^k / k.factorial) t :=
  begin
    convert (hf'.mul (monomial_has_deriv t x)).div_const ((k+1)* k.factorial),
    rw sub_eq_neg_add,
    rw add_comm,
    rw add_div,
    rw [add_right_inj],
    rw [←neg_one_mul, ←neg_one_mul (↑k+1 : ℝ)],
    rw [mul_assoc, mul_comm (↑k+1 : ℝ) ((x - t) ^ k)],
    rw [mul_comm (↑k+1 : ℝ)],
    rw [←mul_assoc, ←mul_assoc],
    rw mul_div_mul_right,
    { simp[neg_div] },
    exact nat.cast_add_one_ne_zero k,
  end,
  convert hk.add this,
  exact (add_sub_cancel'_right _ _).symm,
end

/-- **Taylor's theorem** with the general mean value form of the remainder. -/
lemma taylor_mean_remainder {f g g' : ℝ → ℝ} (hf : cont_diff ℝ (n+1) f) (hx : x₀ < x)
  (gcont : continuous_on g (set.Icc x₀ x))
  (gdiff : ∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at g (g' x_1) x_1)
  (g'_ne : ∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → g' x_1 ≠ 0) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - taylor_sum f n x₀ x =
  (iterated_deriv (n+1) f x') * (x - x')^n /n.factorial * (g x - g x₀) / g' x' :=
begin
  have tcont : continuous_on (λ (t : ℝ), taylor_sum f n t x) (set.Icc x₀ x) :=
    (taylor_sum_continuous hf).continuous_on,
  have tdiff : (∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at (λ (t : ℝ), taylor_sum f n t x)
    ((λ (t : ℝ), iterated_deriv (n + 1) f t * (x - t) ^ n / ↑(n.factorial)) x_1) x_1) :=
  begin
    intros y hy,
    simp,
    exact taylor_sum_has_deriv hf,
  end,
  rcases exists_ratio_has_deriv_at_eq_ratio_slope (λ t, taylor_sum f n t x)
    (λ t, (iterated_deriv (n+1) f t) * (x - t)^n /n.factorial) hx tcont tdiff
    g g' gcont gdiff with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [sub_self, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_sub, neg_mul,
    taylor_sum_self] at h,
  rw mul_comm at h,
  rw ←div_left_inj' (g'_ne y hy) at h,
  rw mul_div_cancel _ (g'_ne y hy) at h,
  rw ←h,
end

/-- **Taylor's theorem** with the Lagrange form of the remainder. -/
lemma taylor_mean_remainder_lagrange {f : ℝ → ℝ} (hf : cont_diff ℝ (n+1) f) (hx : x₀ < x):
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - taylor_sum f n x₀ x =
  (iterated_deriv (n+1) f x') * (x - x₀)^(n+1) /(n+1).factorial :=
begin
  have gcont : continuous_on (λ (t : ℝ), (x - t) ^ (n + 1)) (set.Icc x₀ x) :=
  by { refine continuous.continuous_on _, continuity },
  have gdiff : (∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at (λ (t : ℝ), (x - t) ^ (n + 1))
    ((λ (t : ℝ), -(↑n + 1) * (x - t) ^ n) x_1) x_1) :=
  begin
    intros y hy,
    simp only,
    exact monomial_has_deriv y x,
  end,
  have hg' : ∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x →
    (λ (x_1 : ℝ), (λ (t : ℝ), -(↑n + 1) * (x - t) ^ n) x_1) x_1 ≠ 0 :=
  begin
    intros y hy,
    simp only,
    refine mul_ne_zero _ _,
    { rw neg_ne_zero,
      exact nat.cast_add_one_ne_zero n },
    refine pow_ne_zero n _,
    rw [set.mem_Ioo] at hy,
    rw sub_ne_zero,
    exact hy.2.ne.symm,
  end,
  rcases taylor_mean_remainder hf hx gcont gdiff hg' with ⟨y, hy, h⟩,
  use [y, hy],
  have xy_ne : (x - y)^n ≠ 0 :=
  begin
    refine pow_ne_zero _ _,
    rw [set.mem_Ioo] at hy,
    rw sub_ne_zero,
    exact hy.2.ne.symm,
  end,
  simp only [sub_self, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h,
  rw h,
  rw [neg_div, ←div_neg, neg_mul, neg_neg],
  field_simp,
  rw [mul_assoc, mul_comm ((x - y)^n), ←mul_assoc, ←mul_assoc, mul_comm (↑n+1 : ℝ),
    mul_div_mul_right _ _ xy_ne]
end

/-- **Taylor's theorem** with the Cauchy form of the remainder. -/
lemma taylor_mean_remainder_cauchy {f g g' : ℝ → ℝ} (hf : cont_diff ℝ (n+1) f) (hx : x₀ < x) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - taylor_sum f n x₀ x =
  (iterated_deriv (n+1) f x') * (x - x')^n /n.factorial * (x - x₀) :=
begin
  have gcont : continuous_on id (set.Icc x₀ x) :=
  by { refine continuous.continuous_on _, continuity },
  have gdiff : (∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at id
    ((λ (t : ℝ), (1 : ℝ)) x_1) x_1) := λ _ _, has_deriv_at_id _,
  rcases taylor_mean_remainder hf hx gcont gdiff (λ _ _, by simp) with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [id.def, div_one] at h,
  exact h,
end
