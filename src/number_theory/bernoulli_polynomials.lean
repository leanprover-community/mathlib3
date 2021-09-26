/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import data.nat.choose.cast
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

end bernoulli_poly
