/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.iterated_deriv
import analysis.calculus.mean_value
import measure_theory.integral.interval_integral

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

variables {f : ℝ → ℝ} {n : ℕ} (x₀ : ℝ) (x : ℝ)

/-- The Taylor polynomial. -/
noncomputable
def taylor_sum (f : ℝ → ℝ) (n : ℕ) (x₀ : ℝ) (x : ℝ) : ℝ :=
∑ k in finset.range (n+1), (iterated_deriv k f x₀) * (x - x₀)^k / k.factorial

lemma taylor_sum_succ {f : ℝ → ℝ} {n : ℕ} {x₀ x : ℝ} :
  taylor_sum f (n+1) x₀ x = taylor_sum f n x₀ x +
  iterated_deriv (n + 1) f x₀ * (x - x₀) ^ (n + 1) / ((↑n + 1) * ↑(n.factorial)) :=
begin
  dunfold taylor_sum,
  rw finset.sum_range_succ,
  simp,
end

/-- For `x₀ = x` the Taylor polynomial is just `f x`. -/
@[simp] lemma taylor_sum_self {f : ℝ → ℝ} {n : ℕ} {x : ℝ} : taylor_sum f n x x = f x :=
begin
  induction n with k hk,
  { dunfold taylor_sum, simp },
  rw [taylor_sum_succ, hk],
  simp,
end

/-- If `f` is `n` times continuous differentiable, then the Taylor polynomial is continuous in the
  second variable. -/
lemma taylor_sum_continuous {f : ℝ → ℝ} (hf : cont_diff ℝ (n+1) f) {x : ℝ} :
  continuous (λ t, taylor_sum f n t x) :=
begin
  dunfold taylor_sum,
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
  { dunfold taylor_sum,
    simp only [finset.range_one, finset.sum_singleton, iterated_deriv_zero, pow_zero, mul_one,
      nat.factorial_zero, nat.cast_one, div_one, iterated_deriv_one, has_deriv_at_deriv_iff],
    rw [with_top.coe_zero, zero_add] at hf,
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

/-- **Taylor's theorem** with the Lagrange form of the remainder. -/
lemma taylor_mean_remainder {f : ℝ → ℝ} (hf : cont_diff ℝ (n+1) f) (hx : x₀ < x):
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - taylor_sum f n x₀ x =
  (iterated_deriv (n+1) f x') * (x - x₀)^(n+1) /(n+1).factorial :=
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
  have gcont : continuous_on (λ (t : ℝ), (x - t) ^ (n + 1)) (set.Icc x₀ x) :=
  begin
    refine continuous.continuous_on _,
    continuity,
  end,
  have gdiff : (∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at (λ (t : ℝ), (x - t) ^ (n + 1))
    ((λ (t : ℝ), -(↑n + 1) * (x - t) ^ n) x_1) x_1) :=
  begin
    intros y hy,
    simp only,
    exact monomial_has_deriv y x,
  end,
  rcases exists_ratio_has_deriv_at_eq_ratio_slope (λ t, taylor_sum f n t x)
    (λ t, (iterated_deriv (n+1) f t) * (x - t)^n /n.factorial) hx tcont tdiff
    (λ t, (x - t)^(n+1)) (λ t, -(n+1) * (x - t)^n) gcont gdiff with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [sub_self, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_sub, neg_mul,
    taylor_sum_self] at h,
  have xy_ne : (x - y)^n ≠ 0 :=
  begin
    refine pow_ne_zero _ _,
    rw [set.mem_Ioo] at hy,
    rw sub_ne_zero,
    exact hy.2.ne.symm,
  end,
  have nxy_ne : -(((↑n : ℝ) + 1) * (x - y)^n) ≠ 0 :=
  begin
    rw neg_ne_zero,
    exact mul_ne_zero (nat.cast_add_one_ne_zero n) xy_ne,
  end,
  rw ←div_left_inj' nxy_ne at h,
  rw ←mul_neg at h,
  rw mul_div_cancel _ nxy_ne at h,
  field_simp at h,
  rw div_neg at h,
  rw neg_div at h,
  rw neg_neg at h,
  rw ←mul_assoc at h,
  rw ←mul_assoc at h,
  rw mul_div_mul_right _ _ xy_ne at h,
  simp[←h, mul_comm],
end
