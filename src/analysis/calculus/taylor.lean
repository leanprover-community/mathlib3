/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.iterated_deriv
import analysis.calculus.mean_value
import measure_theory.integral.interval_integral
import data.polynomial.basic
import data.polynomial.module

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
variables [normed_add_comm_group E] [normed_space ℝ E]

namespace polynomial_module

variables {R S M N : Type*}
variables [comm_ring R] [add_comm_group M] [module R M]

variables [semiring S] [add_comm_group N] [module S N]
variables (σ : R →+* S) (f : M →ₛₗ[σ] N) (x : S)

/-- Evaluate a polynomial `p` given a ring hom `σ`, a semilinear map `f`,
and a value `x` for the variable in the target -/
def eval₂ (p : polynomial_module R M) : N :=
p.sum (λ e a, x ^ e • f a)

variables {σ f}

variables {p q : polynomial_module R M}

lemma eval₂_eq_sum {x : S} : p.eval₂ σ f x = p.sum (λ e a, x ^ e • f a) := rfl

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R → polynomial_module R M → M := eval₂ (ring_hom.id _) (linear_map.id)

@[simp] lemma eval_add {x : R} : (p + q).eval x = p.eval x + q.eval x := sorry

lemma eval_eq_sum {x : R} : p.eval x = p.sum (λ e a, x ^ e • a) := rfl

-- We cannot invoke `eval₂` since `q` is a polynomial and not a scalar
noncomputable
def comp (p : polynomial_module R M) (q : polynomial R) : polynomial_module R M :=
p.sum (λ e a, q^e • polynomial_module.single R 0 a)

@[simp] lemma eval_comp {p : polynomial_module R M} {q : polynomial R} {x : R} :
  (p.comp q).eval x = p.eval (q.eval x) := sorry

@[simp] lemma eval_monomial {a : M} {i : ℕ} {x : R} :
  (polynomial_module.single R i a).eval x = x^i • a := sorry

end polynomial_module

/-- The `k`th coefficient of the Taylor polynomial. -/
noncomputable
def taylor_coeff_within (f : ℝ → E) (k : ℕ) (s : set ℝ) (x₀ : ℝ) : E :=
(k.factorial : ℝ)⁻¹ • (iterated_deriv_within k f s x₀)

/-- The Taylor polynomial. -/
noncomputable
def taylor_within (f : ℝ → E) (n : ℕ) (s : set ℝ) (x₀ : ℝ) : polynomial_module ℝ E :=
(finset.range (n+1)).sum (λ k,
  (polynomial_module.single ℝ k (taylor_coeff_within f k s x₀)).comp
  (polynomial.X - polynomial.C x₀))

lemma taylor_within_succ {f : ℝ → E} {n : ℕ} {s : set ℝ} {x₀ : ℝ} :
  taylor_within f (n+1) s x₀ = taylor_within f n s x₀
  + (polynomial_module.single ℝ (n+1) (taylor_coeff_within f (n+1) s x₀)).comp
  (polynomial.X - polynomial.C x₀) :=
begin
  dunfold taylor_within,
  rw finset.sum_range_succ,
end

@[simp] lemma taylor_within_eval_succ {f : ℝ → E} {n : ℕ} {s : set ℝ} {x₀ x : ℝ} :
  (taylor_within f (n+1) s x₀).eval x = (taylor_within f n s x₀).eval x
  + (((↑n + 1) * ↑(n.factorial))⁻¹ * (x - x₀)^(n+1)) • iterated_deriv_within (n + 1) f s x₀ :=
begin
  rw [taylor_within_succ],
  rw [polynomial_module.eval_add],
  congr,
  simp only [polynomial_module.eval_comp, polynomial.eval_sub, polynomial.eval_X, polynomial.eval_C,
    polynomial_module.eval_monomial, mul_inv_rev],
  dunfold taylor_coeff_within,
  rw [←mul_smul, mul_comm, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one,
    mul_inv_rev],
end

/-- The Taylor polynomial of order zero evaluates to `f x`. -/
@[simp] lemma taylor_within_zero_eval {f : ℝ → E} {s : set ℝ} {x₀ x : ℝ} :
  (taylor_within f 0 s x₀).eval x = f x₀ :=
begin
  dunfold taylor_within,
  dunfold taylor_coeff_within,
  simp,
end

/-- Evaluating the Taylor polynomial at `x = x₀` yields `f x`. -/
@[simp] lemma taylor_within_eval_self {f : ℝ → E} {n : ℕ} {s : set ℝ} {x₀ : ℝ} :
  (taylor_within f n s x₀).eval x₀ = f x₀ :=
begin
  induction n with k hk,
  { exact taylor_within_zero_eval },
  simp [hk]
end

lemma taylor_within_apply {f : ℝ → E} {n : ℕ} {s : set ℝ} {x₀ x : ℝ} :
  (taylor_within f n s x₀).eval x = ∑ k in finset.range (n+1),
    ((k.factorial : ℝ)⁻¹ * (x - x₀)^k) • iterated_deriv_within k f s x₀ :=
begin
  induction n with k hk,
  { simp },
  rw [taylor_within_eval_succ, finset.sum_range_succ, hk],
  simp,
end

/-- If `f` is `n` times continuous differentiable, then the Taylor polynomial is continuous in the
  second variable. -/
lemma taylor_within_eval_continuous_on {f : ℝ → E} {x : ℝ} {n : ℕ} {s : set ℝ}
  (hs : unique_diff_on ℝ s) (hf : cont_diff_on ℝ n f s) :
  continuous_on (λ t, (taylor_within f n s t).eval x) s :=
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
lemma monomial_has_deriv_aux (t x : ℝ) {n : ℕ} :
  has_deriv_at (λ y, (x - y)^(n+1)) ((-(n+1) * (x - t)^n)) t :=
begin
  simp_rw sub_eq_neg_add,
  rw [←neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ←mul_assoc],
  convert @has_deriv_at.pow _ _ _ _ _ (n+1) ((has_deriv_at_id t).neg.add_const x),
  simp only [nat.cast_add, nat.cast_one],
end

lemma taylor_coeff_within_has_deriv_within_at {f : ℝ → E} {x y : ℝ} {k : ℕ} {s s' : set ℝ}
  (hs'_unique : unique_diff_within_at ℝ s' y)
  (hs' : s' ∈ 𝓝 y) (h : s' ⊆ s)
  (hf' : differentiable_on ℝ (iterated_deriv_within (k+1) f s) s') :
  has_deriv_within_at (λ t,
    (((k+1 : ℝ) * k.factorial)⁻¹ * (x - t)^(k+1)) • iterated_deriv_within (k+1) f s t)
    ((((k+1 : ℝ) * k.factorial)⁻¹ * (x - y)^(k+1)) • iterated_deriv_within (k+2) f s y -
    ((k.factorial : ℝ)⁻¹ * (x - y)^k) • iterated_deriv_within (k+1) f s y) s' y :=
begin
  have hf'' : has_deriv_within_at (λ t, iterated_deriv_within (k+1) f s t)
    (iterated_deriv_within (k+2) f s y) s' y :=
  begin
    convert (hf' y (mem_of_mem_nhds hs')).has_deriv_within_at,
    rw @iterated_deriv_within_succ _ _ _ _ _ (k.succ) _ _ _ (hs'_unique.mono h),
    refine (deriv_within_subset h hs'_unique _).symm,
    refine differentiable_at.differentiable_within_at _,
    refine hf'.differentiable_at hs',
  end,
  have : has_deriv_within_at (λ t, (((k+1 : ℝ) * k.factorial)⁻¹ * (x - t)^(k+1)))
    (-((k.factorial : ℝ)⁻¹ * (x - y)^k)) s' y :=
  begin
    -- Commuting the factors:
    have : (-((k.factorial : ℝ)⁻¹ * (x - y)^k)) =
      (((k+1 : ℝ) * k.factorial)⁻¹ * (-(k+1) *(x - y)^k)) :=
    by { field_simp [nat.cast_add_one_ne_zero k, nat.factorial_ne_zero k], ring_nf },
    rw this,
    exact (monomial_has_deriv_aux y x).has_deriv_within_at.const_mul _,
  end,
  convert this.smul hf'',
  field_simp[nat.cast_add_one_ne_zero k, nat.factorial_ne_zero k],
  rw neg_div,
  rw neg_smul,
  rw sub_eq_add_neg,
end

lemma taylor_within_eval_has_deriv_within_at {f : ℝ → E} {x y : ℝ} {n : ℕ} {s s' : set ℝ}
  (hs'_unique : unique_diff_within_at ℝ s' y)
  (hs' : s' ∈ 𝓝 y) (h : s' ⊆ s)
  (hf : cont_diff_on ℝ n f s)
  (hf' : differentiable_on ℝ (iterated_deriv_within n f s) s') :
  has_deriv_within_at (λ t, (taylor_within f n s t).eval x)
    (((n.factorial : ℝ)⁻¹ * (x - y)^n) • (iterated_deriv_within (n+1) f s y)) s' y :=
begin
  --have ht' := is_open.mem_nhds is_open_Ioo ht,
  --have unique_Icc := ((unique_diff_within_at_Ioo ht).mono set.Ioo_subset_Icc_self),
  have h'' : unique_diff_on ℝ s := sorry,
  have h''' : y ∈ s := sorry,
  induction n with k hk,
  { simp only [taylor_within_zero_eval, nat.factorial_zero, nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul],
    simp only [iterated_deriv_within_zero] at hf',
    rw iterated_deriv_within_one h'' h''',
    refine has_deriv_within_at.mono _ h,
    refine differentiable_within_at.has_deriv_within_at _,
    refine (hf'.differentiable_at hs').differentiable_within_at.antimono h _,
    refine mem_nhds_within_of_mem_nhds hs',
  },
  simp_rw [nat.add_succ, taylor_within_eval_succ],
  simp only [add_zero, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one],
  have hdiff : differentiable_on ℝ (iterated_deriv_within k f s) s' :=
  begin
    have coe_lt_succ : (k : with_top ℕ) < k.succ :=
    by { rw [with_top.coe_lt_coe], exact lt_add_one k },
    refine differentiable_on.mono _ h,
    exact hf.differentiable_on_iterated_deriv_within coe_lt_succ h'',
  end,
  specialize hk sorry hdiff,
  --specialize hk (cont_diff_on.of_succ hf) hdiff,
  convert hk.add (taylor_coeff_within_has_deriv_within_at hs'_unique hs' h hf'),
  exact (add_sub_cancel'_right _ _).symm,
end

lemma taylor_coeff_within_has_deriv_at {f : ℝ → E} {x y : ℝ} {k : ℕ} {s s' : set ℝ}
  (hs : unique_diff_within_at ℝ s y) (hs' : s' ∈ 𝓝 y)
  (hf' : differentiable_on ℝ (iterated_deriv_within (k+1) f s) s') :
  has_deriv_at (λ t,
    (((k+1 : ℝ) * k.factorial)⁻¹ * (x - t)^(k+1)) • iterated_deriv_within (k+1) f s t)
    ((((k+1 : ℝ) * k.factorial)⁻¹ * (x - y)^(k+1)) • iterated_deriv_within (k+2) f s y -
    ((k.factorial : ℝ)⁻¹ * (x - y)^k) • iterated_deriv_within (k+1) f s y) y :=
begin
  sorry,
end

--/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`. -/
/-lemma taylor_within_eval_has_deriv_within_at {f : ℝ → E} {a b t x : ℝ} {n : ℕ} {s s' : set ℝ}
  (hx : a < b) (ht : t ∈ set.Ioo a b)
  (hf : cont_diff_on ℝ n f (set.Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f s) (set.Ioo a b)) :
  has_deriv_within_at (λ y, (taylor_within f n s y).eval x)
    (((n.factorial : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (set.Icc a b) t)) s' t :=
begin
  have ht' := is_open.mem_nhds is_open_Ioo ht,
  have unique_Icc := ((unique_diff_within_at_Ioo ht).mono set.Ioo_subset_Icc_self),
  induction n with k hk,
  { simp only [taylor_within_zero_eval, iterated_deriv_one, pow_zero, mul_one, nat.factorial_zero,
      nat.cast_one, div_one, has_deriv_at_deriv_iff, zero_add, inv_one, one_smul],
    simp only [iterated_deriv_within_zero] at hf',
    rw iterated_deriv_within_one (unique_diff_on_Icc hx)
      (set.mem_of_subset_of_mem set.Ioo_subset_Icc_self ht),
    rw (hf'.differentiable_at ht').deriv_within unique_Icc,
    exact (hf'.differentiable_at ht').has_deriv_at },
  simp_rw [nat.add_succ, taylor_within_eval_succ],
  simp only [add_zero, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one],
  have hdiff : differentiable_on ℝ (iterated_deriv_within k f (set.Icc a b)) (set.Ioo a b) :=
  begin
    have coe_lt_succ : (k : with_top ℕ) < k.succ :=
    by { rw [with_top.coe_lt_coe], exact lt_add_one k },
    refine differentiable_on.mono _ set.Ioo_subset_Icc_self,
    exact hf.differentiable_on_iterated_deriv_within coe_lt_succ (unique_diff_on_Icc hx),
  end,
  specialize hk sorry hdiff,
  --specialize hk (cont_diff_on.of_succ hf) hdiff,
  convert hk.add (taylor_coeff_within_has_deriv unique_Icc ht' hf'),
  exact (add_sub_cancel'_right _ _).symm,
end-/

lemma taylor_coeff_within_has_deriv {f : ℝ → E} {x y : ℝ} {k : ℕ} {s s' : set ℝ}
  (hs : unique_diff_within_at ℝ s y) (hs' : s' ∈ 𝓝 y)
  (hf' : differentiable_on ℝ (iterated_deriv_within (k+1) f s) s') :
  has_deriv_at (λ t,
    (((k+1 : ℝ) * k.factorial)⁻¹ * (x - t)^(k+1)) • iterated_deriv_within (k+1) f s t)
    ((((k+1 : ℝ) * k.factorial)⁻¹ * (x - y)^(k+1)) • iterated_deriv_within (k+2) f s y -
    ((k.factorial : ℝ)⁻¹ * (x - y)^k) • iterated_deriv_within (k+1) f s y) y :=
begin
  have hf'' : has_deriv_at (λ t, iterated_deriv_within (k+1) f s t)
    (iterated_deriv_within (k+2) f s y) y :=
  begin
    convert hf'.has_deriv_at hs',
    rw @iterated_deriv_within_succ _ _ _ _ _ (k.succ) _ _ _ hs,
    exact (hf'.differentiable_at hs').deriv_within hs,
  end,
  have : has_deriv_at (λ t, (((k+1 : ℝ) * k.factorial)⁻¹ * (x - t)^(k+1)))
    (-((k.factorial : ℝ)⁻¹ * (x - y)^k)) y :=
  begin
    -- Commuting the factors:
    have : (-((k.factorial : ℝ)⁻¹ * (x - y)^k)) =
      (((k+1 : ℝ) * k.factorial)⁻¹ * (-(k+1) *(x - y)^k)) :=
    by { field_simp [nat.cast_add_one_ne_zero k, nat.factorial_ne_zero k], ring_nf },
    rw this,
    refine (monomial_has_deriv_aux y x).const_mul _,
  end,
  convert this.smul hf'',
  field_simp[nat.cast_add_one_ne_zero k, nat.factorial_ne_zero k],
  rw neg_div,
  rw neg_smul,
  rw sub_eq_add_neg,
end

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`. -/
lemma taylor_within_eval_has_deriv {f : ℝ → E} {a b t x : ℝ} {n : ℕ}
  (hx : a < b) (ht : t ∈ set.Ioo a b)
  (hf : cont_diff_on ℝ n f (set.Icc a b))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc a b)) (set.Ioo a b)) :
  has_deriv_at (λ y, (taylor_within f n (set.Icc a b) y).eval x)
    (((n.factorial : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (set.Icc a b) t)) t :=
begin
  have ht' := is_open.mem_nhds is_open_Ioo ht,
  have unique_Icc := ((unique_diff_within_at_Ioo ht).mono set.Ioo_subset_Icc_self),
  induction n with k hk,
  { simp only [taylor_within_zero_eval, iterated_deriv_one, pow_zero, mul_one, nat.factorial_zero,
      nat.cast_one, div_one, has_deriv_at_deriv_iff, zero_add, inv_one, one_smul],
    simp only [iterated_deriv_within_zero] at hf',
    rw iterated_deriv_within_one (unique_diff_on_Icc hx)
      (set.mem_of_subset_of_mem set.Ioo_subset_Icc_self ht),
    rw (hf'.differentiable_at ht').deriv_within unique_Icc,
    exact (hf'.differentiable_at ht').has_deriv_at },
  simp_rw [nat.add_succ, taylor_within_eval_succ],
  simp only [add_zero, nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one],
  have hdiff : differentiable_on ℝ (iterated_deriv_within k f (set.Icc a b)) (set.Ioo a b) :=
  begin
    have coe_lt_succ : (k : with_top ℕ) < k.succ :=
    by { rw [with_top.coe_lt_coe], exact lt_add_one k },
    refine differentiable_on.mono _ set.Ioo_subset_Icc_self,
    exact hf.differentiable_on_iterated_deriv_within coe_lt_succ (unique_diff_on_Icc hx),
  end,
  specialize hk sorry hdiff,
  --specialize hk (cont_diff_on.of_succ hf) hdiff,
  convert hk.add (taylor_coeff_within_has_deriv unique_Icc ht' hf'),
  exact (add_sub_cancel'_right _ _).symm,
end

/-- **Taylor's theorem** with the general mean value form of the remainder. -/
lemma taylor_mean_remainder {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x)) (set.Ioo x₀ x))
  (hx : x₀ < x)
  (gcont : continuous_on g (set.Icc x₀ x))
  (gdiff : ∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at g (g' x_1) x_1)
  (g'_ne : ∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → g' x_1 ≠ 0) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - (taylor_within f n (set.Icc x₀ x) x₀).eval x =
  ((x - x')^n /n.factorial * (g x - g x₀) / g' x') • (iterated_deriv_within (n+1) f (set.Icc x₀ x) x')
  :=
begin
  rcases exists_ratio_has_deriv_at_eq_ratio_slope (λ t, (taylor_within f n (set.Icc x₀ x) t).eval x)
    (λ t, ((n.factorial : ℝ)⁻¹ * (x - t)^n) • (iterated_deriv_within (n+1) f (set.Icc x₀ x) t)) hx
    (taylor_within_eval_continuous_on (unique_diff_on_Icc hx) hf)
    (λ _ hy, taylor_within_eval_has_deriv hx hy hf hf')
    g g' gcont gdiff with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [taylor_within_eval_self] at h,
  rw [mul_comm, ←div_left_inj' (g'_ne y hy), mul_div_cancel _ (g'_ne y hy)] at h,
  rw ←h,
  field_simp [g'_ne y hy, nat.factorial_ne_zero n],
  ring,
end

/-- **Taylor's theorem** with the Lagrange form of the remainder. -/
lemma taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x)) (set.Ioo x₀ x))
  (hx : x₀ < x) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - (taylor_within f n (set.Icc x₀ x) x₀).eval x =
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
  rcases taylor_mean_remainder hf hf' hx gcont (λ y _, monomial_has_deriv_aux y x) hg'
    with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [sub_self, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h,
  rw [h, neg_div, ←div_neg, neg_mul, neg_neg],
  field_simp [nat.cast_add_one_ne_zero n, nat.factorial_ne_zero n, xy_ne y hy],
  ring,
end

/-- **Taylor's theorem** with the Cauchy form of the remainder. -/
lemma taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x)) (set.Ioo x₀ x))
  (hx : x₀ < x) :
  ∃ (x' : ℝ) (hx' : x' ∈ set.Ioo x₀ x), f x - (taylor_within f n (set.Icc x₀ x) x₀).eval x =
  (iterated_deriv_within (n+1) f (set.Icc x₀ x) x') * (x - x')^n /n.factorial * (x - x₀) :=
begin
  have gcont : continuous_on id (set.Icc x₀ x) :=
  by { refine continuous.continuous_on _, continuity },
  have gdiff : (∀ (x_1 : ℝ), x_1 ∈ set.Ioo x₀ x → has_deriv_at id
    ((λ (t : ℝ), (1 : ℝ)) x_1) x_1) := λ _ _, has_deriv_at_id _,
  rcases taylor_mean_remainder hf hf' hx gcont gdiff (λ _ _, by simp) with ⟨y, hy, h⟩,
  use [y, hy],
  simp only [id.def, div_one] at h,
  rw h,
  field_simp [nat.factorial_ne_zero n],
  ring,
end

#check @norm_image_sub_le_of_norm_deriv_le_segment'
#check has_deriv_at.has_deriv_within_at

-- Todo: Vector valued version: norm_image_sub_le_of_norm_deriv_le_segment'

lemma taylor_mean {f : ℝ → E} {a b x : ℝ} {n : ℕ}
  (hf : cont_diff_on ℝ n f (set.Icc x₀ x₁))
  (hf' : differentiable_on ℝ (iterated_deriv_within n f (set.Icc x₀ x₁)) (set.Icc x₀ x₁))
  (hx : x₀ < x₁) : true :=
begin
  --have hf'_within : ∀ (y : ℝ) (y ∈ set.Icc a b),
  --  has_deriv_within_at
  --have norm_image_sub_le_of_norm_deriv_le_segment',
  sorry,
end
