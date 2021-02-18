/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ashvni Narayanan
-/

import number_theory.bernoulli

/-!
# Bernoulli polynomials

The Bernoulli polynomials are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n^{th}$ Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n χoose k} (-1)^k * B_k * X^{n - k} $$
where $B_k$ is the $k^{th}$ Bernoulli number. The Bernoulli polynomials are generating functions,
$$ t * e^{tX} / (e^t - 1) = ∑_{n = 0}^{∞} B_n(X) * ¼{t^n}{n!} $$

## Implementation detail

The Bernoulli (negative) numbers are first defined, `bernoulli_neg`, in order to make proving
theorems using Bernoulli polynomials easier.

## Main theorems

`sum_bernoulli_neg : ∑ k in range n, (n.choose k : ℚ) * bernoulli_neg k = 0`
`sum_bernoulli_poly : ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k = `
  `polynomial.monomial n (n + 1 : ℚ)`
`exp_bernoulli_poly : power_series.mk (λ n, (polynomial.aeval t ((1 / nat.factorial n : ℚ) • `
`  bernoulli_poly n))) * (exp A - 1) = X * rescale t (exp A) `
-/

noncomputable theory
open_locale big_operators
open_locale nat

open nat finset

/-- The negative Bernoulli numbers are defined to be the Bernoulli numbers with a parity sign. -/
def bernoulli_neg (n : ℕ) : ℚ := (-1)^n * (bernoulli n)

@[simp] lemma bernoulli_neg_zero  : bernoulli_neg 0 = 1 := rfl

@[simp] lemma bernoulli_neg_one   : bernoulli_neg 1 = -1/2 :=
by { rw [bernoulli_neg, bernoulli_one], linarith, }

theorem ber_neg_eq_ber : ∀ n : ℕ, n ≠ 1 → bernoulli_neg n = bernoulli n :=
begin
  rintros n hn, by_cases n = 0,
  { rw h, simp, },
  rw [bernoulli_neg, neg_one_pow_eq_pow_mod_two], by_cases k : n%2 = 1,
  { rw k, simp only [neg_mul_eq_neg_mul_symm, one_mul, pow_one],
    have f : 1 < n := by { apply one_lt_iff_ne_zero_and_ne_one.2 ⟨h, hn⟩, },
    have g := bernoulli_odd_eq_zero (odd_iff.2 k) f,
    rw [g, neg_zero], },
  simp only [mod_two_ne_one, ne.def] at *, rw k, simp,
end

@[simp] theorem sum_bernoulli_neg (n : ℕ) ( h : 2 ≤ n ) :
  ∑ k in range n, (n.choose k : ℚ) * bernoulli_neg k = 0 :=
begin
  cases n, { norm_num at * },
  rw [sum_range_succ', bernoulli_neg_zero, mul_one, choose_zero_right, cast_one],
  cases n, { norm_num at * },
  { rw sum_range_succ', simp only [cast_succ, bernoulli_neg_one, choose_one_right],
    have f := sum_bernoulli n.succ.succ,
    rw [sum_range_succ', sum_range_succ'] at f,
    simp only [one_div, bernoulli_one, cast_succ, mul_one, cast_one, add_left_inj,
      choose_zero_right, bernoulli_zero, zero_add, choose_one_right] at f,
    conv_lhs { congr, { congr, { apply_congr, skip,
      rw ber_neg_eq_ber, skip, apply_congr succ_succ_ne_one x, }, }, },
    have g := eq_sub_iff_add_eq.2 f,
    rw g, ring, },
end

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers. -/
def bernoulli_poly (n : ℕ) : polynomial ℚ :=
  ∑ i in range (n + 1), polynomial.monomial (n - i) ((bernoulli_neg i) * (nat.choose n i))

lemma bernoulli_poly_def (n : ℕ) : bernoulli_poly n =
  ∑ i in range (n + 1), polynomial.monomial i ((bernoulli_neg (n - i)) * (nat.choose n i)) :=
begin
  rw [←sum_range_reflect, add_succ_sub_one, add_zero, bernoulli_poly],
  apply sum_congr, {refl,},
  rintros x hx,
  rw mem_range_succ_iff at hx, rw [choose_symm hx, nat.sub_sub_self hx],
end

namespace bernoulli_poly

/-
### examples
-/

section examples

@[simp] lemma bernoulli_poly_zero : bernoulli_poly 0 = 1 :=
by { rw bernoulli_poly, simp, }

@[simp] lemma bernoulli_poly_zero' (n : ℕ) : (bernoulli_poly n).eval 0 = bernoulli_neg n :=
begin
  rw [bernoulli_poly, polynomial.eval_finset_sum], simp only [polynomial.eval_monomial],
  rw sum_range_succ,
  simp only [add_right_eq_self, mul_one, cast_one, nat.sub_self, choose_self, pow_zero],
  apply sum_eq_zero, rintros x hx,
  rw [zero_pow', mul_zero], apply mem_range_sub_ne_zero _ hx,
end

end examples

@[simp] theorem sum_bernoulli_poly (n : ℕ) :
  ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k =
   polynomial.monomial n (n + 1 : ℚ) :=
begin
  cases n,
  { simp only [bernoulli_poly_zero, cast_one, choose_succ_self_right, one_smul,
      polynomial.monomial_zero_left, cast_zero, sum_singleton, zero_add, ring_hom.map_one,
      range_one], },
  simp_rw [bernoulli_poly_def, finset.smul_sum, finset.range_eq_Ico, ←finset.dependent_double_sum,
    finset.sum_Ico_eq_sum_range],
  simp only [cast_succ, nat.add_sub_cancel_left, nat.sub_zero, zero_add, linear_map.map_add],
  simp_rw [polynomial.smul_monomial, mul_comm (bernoulli_neg _) _, smul_eq_mul, ←mul_assoc],
  conv_lhs { apply_congr, skip, conv
    { apply_congr, skip,
      rw [choose_mul ((nat.le_sub_left_iff_add_le (mem_range_le _ H)).1 (mem_range_le _ H_1))
        (le.intro rfl), add_comm x x_1, nat.add_sub_cancel, mul_assoc, mul_comm, ←smul_eq_mul,
        ←polynomial.smul_monomial], },
    rw [←sum_smul], },
  rw sum_range_succ,
  simp only [add_right_eq_self, cast_succ, mul_one, cast_one, cast_add, nat.add_sub_cancel_left,
    choose_succ_self_right, one_smul, bernoulli_neg_zero, sum_singleton, zero_add,
    linear_map.map_add, range_one],
  have f : ∀ x ∈ range n.succ, 2 ≤ n.succ + 1 - x,
  { rintros x H,
    rw [succ_sub (ge_iff_le.1 (mem_range_le _ H)), succ_le_succ_iff,
      succ_sub (ge_iff_le.1 (mem_range_succ_iff.1 H)), succ_le_succ_iff], norm_num, },
  conv_lhs { apply_congr, skip, rw [sum_bernoulli_neg _ (f x H), zero_smul], },
  simp,
end

open power_series
variables {A : Type*} [integral_domain A] [algebra ℚ A] [char_zero A]

theorem exp_bernoulli_poly (t : A) :
  power_series.mk (λ n, (polynomial.aeval t ((1 / nat.factorial n : ℚ) • bernoulli_poly n)))
    * (exp A - 1) = X * rescale t (exp A) :=
begin
  ext, rw [coeff_mul, coeff_mul, nat.sum_antidiagonal_eq_sum_range_succ_mk,
    nat.sum_antidiagonal_eq_sum_range_succ_mk],
  simp only [coeff_mk, coeff_one, coeff_exp, ring_hom.id_apply, linear_map.map_sub, factorial,
    rat.algebra_map_rat_rat],
  rw sum_range_succ,
  have f : ∀ x ∈ range n, ite (n - x = 0) 1 0 = (0 : A),
  { rintros x hx, split_ifs,
    { exfalso, apply mem_range_sub_ne_zero _ hx h, }, refl, },
  conv_lhs { congr, skip, apply_congr, skip, rw f x H, },
  cases n, { simp only [one_div, alg_hom.map_smul, power_series.coeff_zero_eq_constant_coeff,
    add_zero, polynomial.aeval_one, if_congr, mul_one, nat.nat_zero_eq_zero,
    bernoulli_poly.bernoulli_poly_zero, nat.factorial_zero, if_true, nat.zero_sub,
    power_series.constant_coeff_X, nat.sub_self, sum_empty, eq_self_iff_true, nat.factorial_one,
    one_smul, sub_zero, range_zero, power_series.coeff_rescale, ring_hom.map_one, nat.cast_one,
    div_one, sum_singleton, range_one, mul_zero, pow_zero, power_series.coeff_exp, sum_congr,
    sub_self, algebra.smul_mul_assoc], },
  symmetry, rw [sum_eq_single 1],
  { rw [one_div, alg_hom.map_smul, nat.succ_sub_succ_eq_sub, nat.sub_self, nat.factorial_zero,
      power_series.coeff_one_X, one_mul, nat.sub_zero, coeff_rescale, coeff_exp, nat.factorial_one,
      nat.cast_one, div_one],
    simp only [one_div, alg_hom.map_smul, if_true, eq_self_iff_true, sub_zero, zero_add,
      ring_hom.map_one, mul_zero, sub_self, algebra.smul_mul_assoc],
    rw [mul_comm, smul_zero, zero_add],
    suffices g : (algebra_map ℚ A) (↑n!)⁻¹ * (n.succ : ℚ) • t ^ n =
      (n.succ : ℚ) • ∑ (x : ℕ) in range n.succ, (↑x!)⁻¹ • ((polynomial.aeval t) (bernoulli_poly x)
        * (algebra_map ℚ A) (↑(n.succ - x)!)⁻¹),
    { rw [algebra.mul_smul_comm, algebra.smul_def, algebra.smul_def, mul_eq_mul_left_iff] at g,
      cases g with g1 g2, { assumption, },
      { exfalso, apply succ_ne_zero n,
        simp only [ring_hom.map_nat_cast, cast_succ, ring_hom.map_add, ring_hom.map_one] at g2,
        norm_cast at *, }, },
    { have g : (n.succ : ℚ) • t^n = polynomial.aeval t (polynomial.monomial n (n + 1 : ℚ)),
      { rw [polynomial.aeval_monomial, algebra.smul_def], norm_num, },
      rw [g, ←sum_bernoulli_poly, smul_sum, alg_hom.map_sum, mul_sum], apply sum_congr, { refl, },
      { rintros x hx, rw alg_hom.map_smul, rw ←algebra.smul_def,
        rw [mul_comm ((polynomial.aeval t) (bernoulli_poly x)) _, ←algebra.smul_def, smul_smul,
          smul_smul, ←smul_assoc, algebra.smul_def, algebra.smul_def, mul_eq_mul_right_iff], left,
        rw smul_eq_mul, apply congr_arg _,
        rw [choose_eq_factorial_div_factorial, cast_dvd_char_zero, factorial_succ n, cast_mul,
          cast_mul, div_eq_inv_mul, mul_inv', ←mul_assoc, mul_comm (↑n!)⁻¹ _,
          mul_assoc ↑(n.succ) _ _], symmetry,
        rw [mul_comm ↑(n.succ) _, mul_assoc ((↑x!)⁻¹ * (↑(n + 1 - x)!)⁻¹) _ _, mul_comm ↑(n.succ) _,
         ←mul_assoc (↑n!)⁻¹ _ _, inv_mul_cancel, one_mul],
        { norm_num, apply factorial_ne_zero n, },
        { apply factorial_mul_factorial_dvd_factorial (mem_range_le _ hx), },
        { apply mem_range_le _ hx, }, }, }, },
  { rintros b hb h, rw coeff_X b, split_ifs,
    { exfalso, apply h h_1, },
    { norm_num, }, },
  { rintros h, exfalso, apply h, rw [mem_range_succ_iff, succ_le_succ_iff], apply nat.zero_le _, },
end

end bernoulli_poly
