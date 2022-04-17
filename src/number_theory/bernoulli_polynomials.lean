/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import number_theory.bernoulli

/-!
# Bernoulli polynomials

The Bernoulli polynomials (defined here : https://en.wikipedia.org/wiki/Bernoulli_polynomials)
are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n$-th Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n \choose k} (-1)^k * B_k * X^{n - k} $$
where $B_k$ is the $k$-th Bernoulli number. The Bernoulli polynomials are generating functions,
$$ t * e^{tX} / (e^t - 1) = ∑_{n = 0}^{\infty} B_n(X) * \frac{t^n}{n!} $$

## Implementation detail

Bernoulli polynomials are defined using `bernoulli`, the Bernoulli numbers.

## Main theorems

- `sum_bernoulli_poly`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to n is `(n + 1) * X^n`.
- `exp_bernoulli_poly`: The Bernoulli polynomials act as generating functions for the exponential.

## TODO

- `bernoulli_poly_eval_one_neg` : $$ B_n(1 - x) = (-1)^n*B_n(x) $$
- ``bernoulli_poly_eval_one` : Follows as a consequence of `bernoulli_poly_eval_one_neg`.

-/

noncomputable theory
open_locale big_operators
open_locale nat

open nat finset

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers. -/
def bernoulli_poly (n : ℕ) : polynomial ℚ :=
  ∑ i in range (n + 1), polynomial.monomial (n - i) ((bernoulli i) * (choose n i))

lemma bernoulli_poly_def (n : ℕ) : bernoulli_poly n =
  ∑ i in range (n + 1), polynomial.monomial i ((bernoulli (n - i)) * (choose n i)) :=
begin
  rw [←sum_range_reflect, add_succ_sub_one, add_zero, bernoulli_poly],
  apply sum_congr rfl,
  rintros x hx,
  rw mem_range_succ_iff at hx, rw [choose_symm hx, nat.sub_sub_self hx],
end

namespace bernoulli_poly

/-
### examples
-/

section examples

@[simp] lemma bernoulli_poly_zero : bernoulli_poly 0 = 1 :=
by simp [bernoulli_poly]

@[simp] lemma bernoulli_poly_eval_zero (n : ℕ) : (bernoulli_poly n).eval 0 = bernoulli n :=
begin
 rw [bernoulli_poly, polynomial.eval_finset_sum, sum_range_succ],
  have : ∑ (x : ℕ) in range n, bernoulli x * (n.choose x) * 0 ^ (n - x) = 0,
  { apply sum_eq_zero (λ x hx, _),
    have h : 0 < n - x := nat.sub_pos_of_lt (mem_range.1 hx),
    simp [h] },
  simp [this],
end

@[simp] lemma bernoulli_poly_eval_one (n : ℕ) : (bernoulli_poly n).eval 1 = bernoulli' n :=
begin
  simp only [bernoulli_poly, polynomial.eval_finset_sum],
  simp only [←succ_eq_add_one, sum_range_succ, mul_one, cast_one, choose_self,
    (bernoulli _).mul_comm, sum_bernoulli, one_pow, mul_one, polynomial.eval_C,
    polynomial.eval_monomial],
  by_cases h : n = 1,
  { norm_num [h], },
  { simp [h],
    exact bernoulli_eq_bernoulli'_of_ne_one h, }
end

end examples

@[simp] theorem sum_bernoulli_poly (n : ℕ) :
  ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k =
    polynomial.monomial n (n + 1 : ℚ) :=
begin
 simp_rw [bernoulli_poly_def, finset.smul_sum, finset.range_eq_Ico, ←finset.sum_Ico_Ico_comm,
    finset.sum_Ico_eq_sum_range],
  simp only [cast_succ, nat.add_sub_cancel_left, nat.sub_zero, zero_add, linear_map.map_add],
  simp_rw [polynomial.smul_monomial, mul_comm (bernoulli _) _, smul_eq_mul, ←mul_assoc],
  conv_lhs { apply_congr, skip, conv
    { apply_congr, skip,
      rw [← nat.cast_mul, choose_mul ((nat.le_sub_left_iff_add_le $ mem_range_le H).1
        $ mem_range_le H_1) (le.intro rfl), nat.cast_mul, add_comm x x_1, nat.add_sub_cancel,
        mul_assoc, mul_comm, ←smul_eq_mul, ←polynomial.smul_monomial] },
    rw [←sum_smul], },
  rw [sum_range_succ_comm],
  simp only [add_right_eq_self, cast_succ, mul_one, cast_one, cast_add, nat.add_sub_cancel_left,
    choose_succ_self_right, one_smul, bernoulli_zero, sum_singleton, zero_add,
    linear_map.map_add, range_one],
  apply sum_eq_zero (λ x hx, _),
  have f : ∀ x ∈ range n, ¬ n + 1 - x = 1,
  { rintros x H, rw [mem_range] at H,
    rw [eq_comm],
    exact ne_of_lt (nat.lt_of_lt_of_le one_lt_two (nat.le_sub_left_of_add_le (succ_le_succ H))) },
  rw [sum_bernoulli],
  have g : (ite (n + 1 - x = 1) (1 : ℚ) 0) = 0,
    { simp only [ite_eq_right_iff, one_ne_zero],
      intro h₁,
      exact (f x hx) h₁, },
  rw [g, zero_smul],
end

lemma eq_sum_add (n : ℕ) : (n.succ : ℚ) • bernoulli_poly n =
  polynomial.monomial n (n.succ : ℚ) -
  ∑ k in finset.range n, ((n + 1).choose k : ℚ) • bernoulli_poly k :=
begin
  change _ = (polynomial.monomial n) ((n : ℚ) + 1) - ∑ (k : ℕ) in range n,
    ↑((n + 1).choose k) • bernoulli_poly k,
  rw [←sum_bernoulli_poly n, sum_range_succ, add_comm],
  simp only [cast_succ, choose_succ_self_right, add_sub_cancel],
end

lemma sum_range_pow (n p : ℕ) :
  (p  + 1 : ℚ) * ∑ k in range n, (k : ℚ) ^ p = (bernoulli_poly p.succ).eval n - bernoulli (p.succ) :=
begin
  rw [sum_range_pow, bernoulli_poly_def, polynomial.eval_finset_sum, ←sum_div,
    mul_div_cancel' _ _],
  { simp_rw [polynomial.eval_monomial],
    symmetry,
    rw [←sum_flip _, sum_range_succ],
    simp only [mul_one, cast_one, nat.sub_self, choose_zero_right, add_sub_cancel, sub_zero',
      pow_zero],
    apply sum_congr rfl (λ x hx, _),
    apply congr_arg2,
    { apply congr_arg2,
      { congr, apply nat.sub_sub_self (mem_range_le hx), },
      { symmetry, rw ←choose_symm (mem_range_le hx), }, },
    { refl, }, },
  { norm_cast, apply succ_ne_zero _, },
end

lemma succ_eval (n p : ℕ) : (bernoulli_poly p.succ).eval n =
  bernoulli (p.succ) + (p  + 1 : ℚ) * ∑ k in range n, (k : ℚ) ^ p :=
by { apply eq_add_of_sub_eq', rw sum_range_pow, }

lemma polynomial.monomial_eval_one_add_sub (d : ℕ) (x : ℚ) :
  polynomial.eval (1 + x) ((polynomial.monomial d) (succ d : ℚ)) -
    polynomial.eval x ((polynomial.monomial d) (succ d : ℚ)) =
  ∑ (x_1 : ℕ) in range (d + 1), ↑((d + 1).choose x_1) * (↑x_1 * x ^ (x_1 - 1)) :=
begin
  rw [polynomial.eval_monomial, polynomial.eval_monomial, add_comm, add_pow],
  conv_lhs { congr, congr, skip, apply_congr, skip, rw one_pow, rw mul_one, rw mul_comm, },
  rw [sum_range_succ, mul_add, choose_self, cast_one, one_mul, add_sub_cancel, mul_sum,
    sum_range_succ', cast_zero, zero_mul, mul_zero, add_zero],
  apply sum_congr rfl (λ y hy, _),
  rw [←mul_assoc, ←mul_assoc, ←cast_mul, succ_mul_choose_eq, cast_mul, nat.add_sub_cancel],
end

lemma eval_sum_one (n : ℕ) (x : ℚ) :
  (bernoulli_poly n).eval (1 + x) = (bernoulli_poly n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n (λ d hd, _),
  apply (mul_right_inj' _).1, -- if I remove this, the d and hd disappear
  swap 3, exact d.succ,
  swap 3, { norm_cast, apply d.succ_ne_zero, },
  rw [←polynomial.eval_smul, eq_sum_add, mul_add, ←polynomial.eval_smul, eq_sum_add,
    polynomial.eval_sub, polynomial.eval_finset_sum],
  conv_lhs { congr, skip, apply_congr, skip, rw polynomial.eval_smul,
    rw hd x_1 (mem_range.1 H), },
  rw [polynomial.eval_sub, polynomial.eval_finset_sum],
  simp_rw [polynomial.eval_smul, mul_add],
  rw [sum_add_distrib, sub_add, sub_eq_sub_iff_sub_eq_sub, _root_.add_sub_sub_cancel],
  conv_rhs { congr, skip, congr, rw succ_eq_add_one, rw ←choose_succ_self_right d, },
  rw [←sum_range_succ _ d, polynomial.monomial_eval_one_add_sub],
end

open power_series
open polynomial (aeval)
variables {A : Type*} [comm_ring A] [algebra ℚ A]

-- TODO: define exponential generating functions, and use them here
-- This name should probably be updated afterwards

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`  -/
theorem exp_bernoulli_poly' (t : A) :
  mk (λ n, aeval t ((1 / n! : ℚ) • bernoulli_poly n)) * (exp A - 1) = X * rescale t (exp A) :=
begin
  -- check equality of power series by checking coefficients of X^n
  ext n,
  -- n = 0 case solved by `simp`
  cases n, { simp },
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul, coeff_rescale, coeff_exp, coeff_mul,
    nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ],
  -- last term is zero so kill with `add_zero`
  simp only [ring_hom.map_sub, nat.sub_self, constant_coeff_one, constant_coeff_exp,
    coeff_zero_eq_constant_coeff, mul_zero, sub_self, add_zero],
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  set u : units ℚ := ⟨(n+1)!, (n+1)!⁻¹,
    mul_inv_cancel (by exact_mod_cast factorial_ne_zero (n+1)),
      inv_mul_cancel (by exact_mod_cast factorial_ne_zero (n+1))⟩ with hu,
  rw ←units.mul_right_inj (units.map (algebra_map ℚ A).to_monoid_hom u),
  -- now tidy up unit mess and generally do trivial rearrangements
  -- to make RHS (n+1)*t^n
  rw [units.coe_map, mul_left_comm, ring_hom.to_monoid_hom_eq_coe,
      ring_hom.coe_monoid_hom, ←ring_hom.map_mul, hu, units.coe_mk],
  change _ = t^n * algebra_map ℚ A (((n+1)*n! : ℕ)*(1/n!)),
  rw [cast_mul, mul_assoc, mul_one_div_cancel
    (show (n! : ℚ) ≠ 0, from cast_ne_zero.2 (factorial_ne_zero n)), mul_one, mul_comm (t^n),
    ← polynomial.aeval_monomial, cast_add, cast_one],
  -- But this is the RHS of `sum_bernoulli_poly`
  rw [← sum_bernoulli_poly, finset.mul_sum, alg_hom.map_sum],
  -- and now we have to prove a sum is a sum, but all the terms are equal.
  apply finset.sum_congr rfl,
  -- The rest is just trivialities, hampered by the fact that we're coercing
  -- factorials and binomial coefficients between ℕ and ℚ and A.
  intros i hi,
  -- deal with coefficients of e^X-1
  simp only [nat.cast_choose ℚ (mem_range_le hi), coeff_mk,
    if_neg (mem_range_sub_ne_zero hi), one_div, alg_hom.map_smul, coeff_one, units.coe_mk,
    coeff_exp, sub_zero, linear_map.map_sub, algebra.smul_mul_assoc, algebra.smul_def,
    mul_right_comm _ ((aeval t) _), ←mul_assoc, ← ring_hom.map_mul, succ_eq_add_one],
  -- finally cancel the Bernoulli polynomial and the algebra_map
  congr',
  apply congr_arg,
  rw [mul_assoc, div_eq_mul_inv, ← mul_inv'],
end

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`  -/
theorem exp_bernoulli_poly'' (t : ℚ) :
  mk (λ n, polynomial.eval t ((1 / n! : ℚ) • bernoulli_poly n)) * (exp ℚ - 1) =
    X * rescale t (exp ℚ) :=
begin
  convert exp_bernoulli_poly' t,
  ext,
  simp only [one_div, alg_hom.map_smul, polynomial.eval_smul],
  symmetry, convert smul_eq_mul ℚ,
  { simp only [rat.cast_id, rat.coe_cast_hom], },
  { symmetry,
    rw polynomial.aeval_def, rw polynomial.eval₂_eq_eval_map,
    congr, simp only [polynomial.map_id, rat.algebra_map_rat_rat], },
end

lemma exp_sub_one_ne_zero : exp ℚ - 1 ≠ 0 :=
begin
  intro this,
  rw power_series.ext_iff at this, specialize this 1,
  simp only [linear_map.map_zero, nat.one_ne_zero, factorial_one, coeff_one, cast_one,
  coeff_exp, ring_hom.id_apply, sub_zero, linear_map.map_sub, if_false, one_ne_zero, div_one,
  rat.algebra_map_rat_rat] at this,
  exfalso, assumption,
end

lemma function.smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) :
  (λ n : ℕ, a * (f n)) = a • (λ n : ℕ, f n) := by { ext, simp only [smul_eq_mul, pi.smul_apply], }

lemma power_series.mk_smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) : mk (a • f) = a • mk f :=
by { ext, rw [coeff_mk, coeff_smul, coeff_mk], simp only [smul_eq_mul, pi.smul_apply], }

instance : is_scalar_tower ℚ (power_series ℚ) (power_series ℚ) :=
begin
  convert is_scalar_tower.of_algebra_map_eq _,
  any_goals { ext1, congr, simp only [rat.cast_id, rat.coe_cast_hom], },
  { intro x, simp only [ring_hom.map_rat_algebra_map], },
end

lemma rescale_mk {R : Type*} [comm_semiring R] (f : ℕ → R) (a : R) :
  rescale a (mk f) = mk (λ n : ℕ, a^n * (f n)) :=
by { ext, rw [coeff_rescale, coeff_mk, coeff_mk], }

lemma rescale_comp_eq_mul {R : Type*} [comm_semiring R] (f : power_series R) (a b : R) :
  rescale b (rescale a f) = rescale (a * b) f :=
begin
  ext,
  repeat { rw coeff_rescale, },
  rw [mul_pow, mul_comm _ (b^n), mul_assoc],
end

/-- Bernoulli polynomials multiplication theorem :
  For k ≥ 1, B_m(k*x) = ∑ i in range k, B_m (x + i / k).  -/
theorem eval_mul (m : ℕ) {k : ℕ} (hk : k ≠ 0) (x : ℚ) :
  (bernoulli_poly m).eval ((k : ℚ) * x) =
  k^(m - 1 : ℤ) * ∑ i in range k, (bernoulli_poly m).eval (x + i / k) :=
begin
  have coe_hk : (k : ℚ) ≠ 0,
  { simp only [hk, cast_eq_zero, ne.def, not_false_iff], },
  suffices : (∑ i in range k, (power_series.mk (λ n, (k^(n - 1 : ℤ) : ℚ) *
    (polynomial.eval (x + i / k) ((1 / n! : ℚ) • (bernoulli_poly n))) ))) * ((exp ℚ - 1)  *
    (rescale (k : ℚ) (exp ℚ - 1))) = (power_series.mk (λ n, polynomial.eval ((k : ℚ) * x)
    ((1 / n! : ℚ) • bernoulli_poly n))) * ((exp ℚ - 1) * (rescale (k : ℚ) (exp ℚ - 1))),
  { rw mul_eq_mul_right_iff at this, cases this,
    { rw power_series.ext_iff at this,
      simp only [one_div, coeff_mk, polynomial.eval_smul, factorial, linear_map.map_sum] at this,
      specialize this m,
      have symm := this.symm,
      rw inv_mul_eq_iff_eq_mul' _ at symm,
      { rw [symm, ←mul_sum, ←mul_assoc, ←mul_sum, ←mul_assoc, mul_comm _ (m! : ℚ)⁻¹, ←mul_assoc,
          inv_mul_cancel _, one_mul],
        { norm_cast, apply factorial_ne_zero _, }, },
      { norm_cast, apply factorial_ne_zero _, }, },
    { exfalso, rw mul_eq_zero at this, cases this,
      { apply exp_sub_one_ne_zero this, },
      { apply exp_sub_one_ne_zero,
        rw ←(rescale (k : ℚ)).map_zero at this,
        apply rescale_injective coe_hk this, }, }, },
  { symmetry, rw [←mul_assoc, exp_bernoulli_poly''],
    have : ∀ n : ℕ, (k : ℚ)^(n - 1 : ℤ) = 1 / k * k^n,
    { intro n,
      rw [fpow_sub_one coe_hk, inv_eq_one_div, mul_comm, gpow_coe_nat], },
    conv_rhs { congr, apply_congr, skip, conv { congr, funext, rw [this, mul_assoc], }, },
    conv_rhs { congr, apply_congr, skip, rw [function.smul, power_series.mk_smul, ←rescale_mk], },
    rw [mul_comm (exp ℚ - 1) _, ←mul_assoc, sum_mul],
    conv_rhs { congr, apply_congr, skip, rw [smul_mul_assoc, ←ring_hom.map_mul,
      exp_bernoulli_poly'', ring_hom.map_mul, rescale_comp_eq_mul, add_div_eq_mul_add_div _ _ coe_hk,
      div_mul_cancel _ coe_hk, ←exp_mul_exp_eq_exp_add, ←mul_assoc, ←smul_mul_assoc,
      ←exp_pow_eq_rescale_exp], },
    rw [←mul_sum, ←geom_sum_def, mul_assoc _ _ (exp ℚ - 1), geom_sum_mul, ←smul_mul_assoc],
    apply congr_arg2, apply congr_arg2,
    { ext, rw [coeff_smul, coeff_rescale, coeff_X],
      by_cases n = 1,
      { rw [if_pos h, h, mul_one, pow_one, div_mul_cancel _ coe_hk], },
      { rw [if_neg h, mul_zero, mul_zero], }, },
    { rw mul_comm, },
    { rw [ring_hom.map_sub, exp_pow_eq_rescale_exp], congr, apply (rescale (k : ℚ)).map_one', }, },
end

end bernoulli_poly
