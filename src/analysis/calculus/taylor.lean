/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.iterated_deriv
import analysis.calculus.mean_value
import data.polynomial.basic
import data.polynomial.module

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylor_coeff_within`: the Taylor coefficient using `deriv_within`
* `taylor_within`: the Taylor polynomial using `deriv_within`

## Main statements

* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder
* `exists_taylor_mean_remainder_bound`: Taylor's theorem for vector valued functions with a
polynomial bound on the remainder

## TODO

* the Peano form of the remainder
* the integral form of the remainder
* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/


open_locale big_operators interval topology nat
open set

variables {𝕜 E F : Type*}
variables [normed_add_comm_group E] [normed_space ℝ E]

/-- The `k`th coefficient of the Taylor polynomial. -/
noncomputable
def taylor_coeff_within (f : ℝ → E) (k : ℕ) (s : set ℝ) (x₀ : ℝ) : E :=
(k! : ℝ)⁻¹ • (iterated_deriv_within k f s x₀)

/-- The Taylor polynomial with derivatives inside of a set `s`.

The Taylor polynomial is given by
$$∑_{k=0}^n \frac{(x - x₀)^k}{k!} f^{(k)}(x₀),$$
where $f^{(k)}(x₀)$ denotes the iterated derivative in the set `s`. -/
noncomputable
def taylor_within (f : ℝ → E) (n : ℕ) (s : set ℝ) (x₀ : ℝ) : polynomial_module ℝ E :=
(finset.range (n+1)).sum (λ k,
  polynomial_module.comp (polynomial.X - polynomial.C x₀)
  (polynomial_module.single ℝ k (taylor_coeff_within f k s x₀)))

/-- The Taylor polynomial with derivatives inside of a set `s` considered as a function `ℝ → E`-/
noncomputable
def taylor_within_eval (f : ℝ → E) (n : ℕ) (s : set ℝ) (x₀ x : ℝ) : E :=
polynomial_module.eval x (taylor_within f n s x₀)

lemma taylor_within_succ (f : ℝ → E) (n : ℕ) (s : set ℝ) (x₀ : ℝ) :
  taylor_within f (n+1) s x₀ = taylor_within f n s x₀
  + polynomial_module.comp (polynomial.X - polynomial.C x₀)
  (polynomial_module.single ℝ (n+1) (taylor_coeff_within f (n+1) s x₀)) :=
begin
  dunfold taylor_within,
  rw finset.sum_range_succ,
end

@[simp] lemma taylor_within_eval_succ (f : ℝ → E) (n : ℕ) (s : set ℝ) (x₀ x : ℝ) :
  taylor_within_eval f (n+1) s x₀ x = taylor_within_eval f n s x₀ x
  + (((n + 1 : ℝ) * n!)⁻¹ * (x - x₀)^(n+1)) • iterated_deriv_within (n + 1) f s x₀ :=
begin
  simp_rw [taylor_within_eval, taylor_within_succ, linear_map.map_add, polynomial_module.comp_eval],
  congr,
  simp only [polynomial.eval_sub, polynomial.eval_X, polynomial.eval_C,
    polynomial_module.eval_single, mul_inv_rev],
  dunfold taylor_coeff_within,
  rw [←mul_smul, mul_comm, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one,
    mul_inv_rev],
end

/-- The Taylor polynomial of order zero evaluates to `f x`. -/
@[simp] lemma taylor_within_zero_eval (f : ℝ → E) (s : set ℝ) (x₀ x : ℝ) :
  taylor_within_eval f 0 s x₀ x = f x₀ :=
begin
  dunfold taylor_within_eval,
  dunfold taylor_within,
  dunfold taylor_coeff_within,
  simp,
end

/-- Evaluating the Taylor polynomial at `x = x₀` yields `f x`. -/
@[simp] lemma taylor_within_eval_self (f : ℝ → E) (n : ℕ) (s : set ℝ) (x₀ : ℝ) :
  taylor_within_eval f n s x₀ x₀ = f x₀ :=
begin
  induction n with k hk,
  { exact taylor_within_zero_eval _ _ _ _},
  simp [hk]
end

lemma taylor_within_apply (f : ℝ → E) (n : ℕ) (s : set ℝ) (x₀ x : ℝ) :
  taylor_within_eval f n s x₀ x = ∑ k in finset.range (n+1),
    ((k! : ℝ)⁻¹ * (x - x₀)^k) • iterated_deriv_within k f s x₀ :=
begin
  induction n with k hk,
  { simp },
  rw [taylor_within_eval_succ, finset.sum_range_succ, hk],
  simp,
end

/-- If `f` is `n` times continuous differentiable on a set `s`, then the Taylor polynomial
  `taylor_within_eval f n s x₀ x` is continuous in `x₀`. -/
lemma continuous_on_taylor_within_eval {f : ℝ → E} {x : ℝ} {n : ℕ} {s : set ℝ}
  (hs : unique_diff_on ℝ s) (hf : cont_diff_on ℝ n f s) :
  continuous_on (λ t, taylor_within_eval f n s t x) s :=
begin
  simp_rw taylor_within_apply,
  refine continuous_on_finset_sum (finset.range (n+1)) (λ i hi, _),
  refine (continuous_on_const.mul ((continuous_on_const.sub continuous_on_id).pow _)).smul _,
  rw cont_diff_on_iff_continuous_on_differentiable_on_deriv hs at hf,
  cases hf,
  specialize hf_left i,
  simp only [finset.mem_range] at hi,
  refine (hf_left _),
  simp only [with_top.coe_le_coe],
  exact nat.lt_succ_iff.mp hi,
end

/-- Helper lemma for calculating the derivative of the monomial that appears in Taylor expansions.-/
lemma monomial_has_deriv_aux (t x : ℝ) (n : ℕ) :
  has_deriv_at (λ y, (x - y)^(n+1)) (-(n+1) * (x - t)^n) t :=
begin
  simp_rw sub_eq_neg_add,
  rw [←neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ←mul_assoc],
  convert @has_deriv_at.pow _ _ _ _ _ (n+1) ((has_deriv_at_id t).neg.add_const x),
  simp only [nat.cast_add, nat.cast_one],
end

lemma has_deriv_within_at_taylor_coeff_within {f : ℝ → E} {x y : ℝ} {k : ℕ} {s s' : set ℝ}
  (hs'_unique : unique_diff_within_at ℝ s' y)
  (hs' : s' ∈ 𝓝[s] y) (hy : y ∈ s') (h : s' ⊆ s)
  (hf' : differentiable_on ℝ (iterated_deriv_within (k+1) f s) s') :
  has_deriv_within_at (λ t,
    (((k+1 : ℝ) * k!)⁻¹ * (x - t)^(k+1)) • iterated_deriv_within (k+1) f s t)
    ((((k+1 : ℝ) * k!)⁻¹ * (x - y)^(k+1)) • iterated_deriv_within (k+2) f s y -
    ((k! : ℝ)⁻¹ * (x - y)^k) • iterated_deriv_within (k+1) f s y) s' y :=
begin
  have hf'' : has_deriv_within_at (λ t, iterated_deriv_within (k+1) f s t)
    (iterated_deriv_within (k+2) f s y) s' y :=
  begin
    convert (hf' y hy).has_deriv_within_at,
    rw iterated_deriv_within_succ (hs'_unique.mono h),
    refine (deriv_within_subset h hs'_unique _).symm,
    exact (hf' y hy).antimono h hs',
  end,
  have : has_deriv_within_at (λ t, (((k+1 : ℝ) * k!)⁻¹ * (x - t)^(k+1)))
    (-((k! : ℝ)⁻¹ * (x - y)^k)) s' y :=
  begin
    -- Commuting the factors:
    have : (-((k! : ℝ)⁻¹ * (x - y)^k)) =
      (((k+1 : ℝ) * k!)⁻¹ * (-(k+1) *(x - y)^k)) :=
    by { field_simp [nat.cast_add_one_ne_zero k, nat.factorial_ne_zero k], ring_nf },
    rw this,
    exact (monomial_has_deriv_aux y x _).has_deriv_within_at.const_mul _,
  end,
  convert this.smul hf'',
  field_simp [nat.cast_add_one_ne_zero k, nat.factorial_ne_zero k],
  rw [neg_div, neg_smul, sub_eq_add_neg],
end

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for arbitrary sets -/
lemma has_deriv_within_at_taylor_within_eval {f : ℝ → E} {x y : ℝ} {n : ℕ} {s s' : set ℝ}
  (hs'_unique : unique_diff_within_at ℝ s' y) (hs_unique : unique_diff_on ℝ s)
  (hs' : s' ∈ 𝓝[s] y) (hy : y ∈ s') (h : s' ⊆ s)
  (hf : cont_diff_on ℝ n f s)
  (hf' : differentiable_on ℝ (iterated_deriv_within n f s) s') :
  has_deriv_within_at (λ t, taylor_within_eval f n s t x)
    (((n! : ℝ)⁻¹ * (x - y)^n) • (iterated_deriv_within (n+1) f s y)) s' y :=
begin
  induction n with k hk,
  { simp only [taylor_within_zero_eval, nat.factorial_zero, nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul],
    simp only [iterated_deriv_within_zero] at hf',
    rw iterated_deriv_within_one hs_unique (h hy),
    refine has_deriv_within_at.mono _ h,
    refine differentiable_within_at.has_deriv_within_at _,
    exact (hf' y hy).antimono h hs' },
  simp_rw [nat.add_succ, taylor_within_eval_succ],
  simp only [add_zero, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one],
  have hdiff : differentiable_on ℝ (iterated_deriv_within k f s) s' :=
  begin
    have coe_lt_succ : (k : with_top ℕ) < k.succ :=
    by { rw [with_top.coe_lt_coe], exact lt_add_one k },
    refine differentiable_on.mono _ h,
    exact hf.differentiable_on_iterated_deriv_within coe_lt_succ hs_unique,
  end,
  specialize hk (cont_diff_on.of_succ hf) hdiff,
  convert hk.add (has_deriv_within_at_taylor_coeff_within hs'_unique hs' hy h hf'),
  exact (add_sub_cancel'_right _ _).symm,
end

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for open intervals -/
lemma taylor_within_eval_has_deriv_at_Ioo {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ}
  (hx : a < b) (ht : t ∈ Ioo a b)
  (hf : cont_diff_on ℝ n f (Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Ioo a b)) :
  has_deriv_at (λ y, taylor_within_eval f n (Icc a b) y x)
    (((n! : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (Icc a b) t)) t :=
begin
  have h_nhds := is_open.mem_nhds is_open_Ioo ht,
  exact (has_deriv_within_at_taylor_within_eval (unique_diff_within_at_Ioo ht)
    (unique_diff_on_Icc hx) (nhds_within_le_nhds h_nhds) ht Ioo_subset_Icc_self hf hf')
    .has_deriv_at h_nhds,
end

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for closed intervals -/
lemma has_deriv_within_taylor_within_eval_at_Icc {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ}
  (hx : a < b) (ht : t ∈ Icc a b) (hf : cont_diff_on ℝ n f (Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Icc a b)) :
  has_deriv_within_at (λ y, taylor_within_eval f n (Icc a b) y x)
    (((n! : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (Icc a b) t)) (Icc a b) t :=
has_deriv_within_at_taylor_within_eval (unique_diff_on_Icc hx t ht) (unique_diff_on_Icc hx)
  self_mem_nhds_within ht rfl.subset hf hf'

/-! ### Taylor's theorem with mean value type remainder estimate -/

/-- **Taylor's theorem** with the general mean value form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable in the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`, and `g` is a differentiable function on
`Ioo x₀ x` and continuous on `Icc x₀ x`. Then there exists a `x' ∈ Ioo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{(x - x')^n}{n!} \frac{g(x) - g(x₀)}{g' x'},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$. -/
lemma taylor_mean_remainder {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
  (hf : cont_diff_on ℝ n f (Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc x₀ x)) (Ioo x₀ x))
  (gcont : continuous_on g (Icc x₀ x))
  (gdiff : ∀ (x_1 : ℝ), x_1 ∈ Ioo x₀ x → has_deriv_at g (g' x_1) x_1)
  (g'_ne : ∀ (x_1 : ℝ), x_1 ∈ Ioo x₀ x → g' x_1 ≠ 0) :
  ∃ (x' : ℝ) (hx' : x' ∈ Ioo x₀ x), f x - taylor_within_eval f n (Icc x₀ x) x₀ x =
  ((x - x')^n /n! * (g x - g x₀) / g' x') •
    (iterated_deriv_within (n+1) f (Icc x₀ x) x')
  :=
begin
  -- We apply the mean value theorem
  rcases exists_ratio_has_deriv_at_eq_ratio_slope (λ t, taylor_within_eval f n (Icc x₀ x) t x)
    (λ t, ((n! : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (Icc x₀ x) t)) hx
    (continuous_on_taylor_within_eval (unique_diff_on_Icc hx) hf)
    (λ _ hy, taylor_within_eval_has_deriv_at_Ioo x hx hy hf hf')
    g g' gcont gdiff with ⟨y, hy, h⟩,
  use [y, hy],
  -- The rest is simplifications and trivial calculations
  simp only [taylor_within_eval_self] at h,
  rw [mul_comm, ←div_left_inj' (g'_ne y hy), mul_div_cancel _ (g'_ne y hy)] at h,
  rw ←h,
  field_simp [g'_ne y hy, n.factorial_ne_zero],
  ring,
end

/-- **Taylor's theorem** with the Lagrange form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable in the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`. Then there exists a `x' ∈ Ioo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x₀)^{n+1}}{(n+1)!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
lemma taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
  (hf : cont_diff_on ℝ n f (Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc x₀ x)) (Ioo x₀ x)) :
  ∃ (x' : ℝ) (hx' : x' ∈ Ioo x₀ x), f x - taylor_within_eval f n (Icc x₀ x) x₀ x =
  (iterated_deriv_within (n+1) f (Icc x₀ x) x') * (x - x₀)^(n+1) /(n+1)! :=
begin
  have gcont : continuous_on (λ (t : ℝ), (x - t) ^ (n + 1)) (Icc x₀ x) :=
  by { refine continuous.continuous_on _, continuity },
  have xy_ne : ∀ (y : ℝ), y ∈ Ioo x₀ x → (x - y)^n ≠ 0 :=
  begin
    intros y hy,
    refine pow_ne_zero _ _,
    rw [mem_Ioo] at hy,
    rw sub_ne_zero,
    exact hy.2.ne.symm,
  end,
  have hg' : ∀ (y : ℝ), y ∈ Ioo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 :=
  λ y hy, mul_ne_zero (neg_ne_zero.mpr (nat.cast_add_one_ne_zero n)) (xy_ne y hy),
  -- We apply the general theorem with g(t) = (x - t)^(n+1)
  rcases taylor_mean_remainder hx hf hf' gcont (λ y _, monomial_has_deriv_aux y x _) hg'
    with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [sub_self, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h,
  rw [h, neg_div, ←div_neg, neg_mul, neg_neg],
  field_simp [n.cast_add_one_ne_zero, n.factorial_ne_zero, xy_ne y hy],
  ring,
end

/-- **Taylor's theorem** with the Cauchy form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`. Then there exists a `x' ∈ Ioo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x')^n (x-x₀)}{n!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
lemma taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
  (hf : cont_diff_on ℝ n f (Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc x₀ x)) (Ioo x₀ x)) :
  ∃ (x' : ℝ) (hx' : x' ∈ Ioo x₀ x), f x - taylor_within_eval f n (Icc x₀ x) x₀ x =
  (iterated_deriv_within (n+1) f (Icc x₀ x) x') * (x - x')^n /n! * (x - x₀) :=
begin
  have gcont : continuous_on id (Icc x₀ x) := continuous.continuous_on (by continuity),
  have gdiff : (∀ (x_1 : ℝ), x_1 ∈ Ioo x₀ x → has_deriv_at id
    ((λ (t : ℝ), (1 : ℝ)) x_1) x_1) := λ _ _, has_deriv_at_id _,
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder hx hf hf' gcont gdiff (λ _ _, by simp) with ⟨y, hy, h⟩,
  use [y, hy],
  rw h,
  field_simp [n.factorial_ne_zero],
  ring,
end

/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
The difference of `f` and its `n`-th Taylor polynomial can be estimated by
`C * (x - a)^(n+1) / n!` where `C` is a bound for the `n+1`-th iterated derivative of `f`. -/
lemma taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ}
  (hab : a ≤ b) (hf : cont_diff_on ℝ (n+1) f (Icc a b)) (hx : x ∈ Icc a b)
  (hC : ∀ y ∈ Icc a b, ‖iterated_deriv_within (n + 1) f (Icc a b) y‖ ≤ C) :
  ‖f x - taylor_within_eval f n (Icc a b) a x‖ ≤ C * (x - a)^(n+1) / n! :=
begin
  rcases eq_or_lt_of_le hab with rfl|h,
  { rw [Icc_self, mem_singleton_iff] at hx,
    simp [hx] },
  -- The nth iterated derivative is differentiable
  have hf' : differentiable_on ℝ (iterated_deriv_within n f (Icc a b)) (Icc a b) :=
  hf.differentiable_on_iterated_deriv_within (with_top.coe_lt_coe.mpr n.lt_succ_self)
    (unique_diff_on_Icc h),
  -- We can uniformly bound the derivative of the Taylor polynomial
  have h' : ∀ (y : ℝ) (hy : y ∈ Ico a x),
    ‖((n! : ℝ)⁻¹ * (x - y) ^ n) • iterated_deriv_within (n + 1) f (Icc a b) y‖
    ≤ (n! : ℝ)⁻¹ * |(x - a)|^n * C,
  { rintro y ⟨hay, hyx⟩,
    rw [norm_smul, real.norm_eq_abs],
    -- Estimate the iterated derivative by `C`
    refine mul_le_mul _ (hC y ⟨hay, hyx.le.trans hx.2⟩) (by positivity) (by positivity),
    -- The rest is a trivial calculation
    rw [abs_mul, abs_pow, abs_inv, nat.abs_cast],
    mono* with [0 ≤ (n! : ℝ)⁻¹],
    any_goals { positivity },
    linarith [hx.1, hyx] },
  -- Apply the mean value theorem for vector valued functions:
  have A : ∀ t ∈ Icc a x, has_deriv_within_at (λ y, taylor_within_eval f n (Icc a b) y x)
    (((↑n!)⁻¹ * (x - t) ^ n) • iterated_deriv_within (n + 1) f (Icc a b) t) (Icc a x) t,
  { assume t ht,
    have I : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2,
    exact (has_deriv_within_taylor_within_eval_at_Icc x h (I ht) hf.of_succ hf').mono I },
  have := norm_image_sub_le_of_norm_deriv_le_segment' A h' x (right_mem_Icc.2 hx.1),
  simp only [taylor_within_eval_self] at this,
  refine this.trans_eq _,
  -- The rest is a trivial calculation
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)],
  ring_exp,
end


/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
There exists a constant `C` such that for all `x ∈ Icc a b` the difference of `f` and its `n`-th
Taylor polynomial can be estimated by `C * (x - a)^(n+1)`. -/
lemma exists_taylor_mean_remainder_bound {f : ℝ → E} {a b : ℝ} {n : ℕ}
  (hab : a ≤ b) (hf : cont_diff_on ℝ (n+1) f (Icc a b)) :
  ∃ C, ∀ x ∈ Icc a b, ‖f x - taylor_within_eval f n (Icc a b) a x‖ ≤ C * (x - a)^(n+1) :=
begin
  rcases eq_or_lt_of_le hab with rfl|h,
  { refine ⟨0, λ x hx, _⟩,
    have : a = x, by simpa [← le_antisymm_iff] using hx,
    simp [← this] },
  -- We estimate by the supremum of the norm of the iterated derivative
  let g : ℝ → ℝ := λ y, ‖iterated_deriv_within (n + 1) f (Icc a b) y‖,
  use [has_Sup.Sup (g '' Icc a b) / n!],
  intros x hx,
  rw div_mul_eq_mul_div₀,
  refine taylor_mean_remainder_bound hab hf hx (λ y, _),
  exact (hf.continuous_on_iterated_deriv_within rfl.le $ unique_diff_on_Icc h)
    .norm.le_Sup_image_Icc,
end
