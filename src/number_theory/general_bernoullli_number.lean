/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_polynomials
import number_theory.dirichlet_character

/-!
# General Bernoulli Numbers

This file defines the generalized Bernoulli numbers related to Dirichlet characters
and gives its properties.

## Main definitions
 * `general_bernoulli_number`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

variables {S : Type*} [comm_semiring S] [algebra ℚ S] {n : ℕ} (ψ : dirichlet_character S n)
open dirichlet_character
open_locale big_operators

/-- The generalized Bernoulli number -/
noncomputable def general_bernoulli_number (m : ℕ) : S :=
  (ψ.conductor)^(m - 1) * (∑ a in finset.range ψ.conductor, asso_dirichlet_character ψ a.succ *
    algebra_map ℚ S ((bernoulli_poly m).eval (a.succ / ψ.conductor : ℚ)))
-- def is ind of F

namespace general_bernoulli_number

lemma general_bernoulli_number_def (m : ℕ) : general_bernoulli_number ψ m =
  (ψ.conductor)^(m - 1) * (∑ a in finset.range ψ.conductor, asso_dirichlet_character ψ a.succ *
  algebra_map ℚ S ((bernoulli_poly m).eval (a.succ / ψ.conductor : ℚ))) := rfl

lemma general_bernoulli_number_one_eval_one :
general_bernoulli_number (1 : dirichlet_character S 1) 1 = algebra_map ℚ S (1/2 : ℚ) :=
begin
  rw general_bernoulli_number_def, rw conductor_one nat.one_pos,
  simp only [one_div, one_pow, one_mul, bernoulli'_one, nat.cast_zero,
    bernoulli_poly.bernoulli_poly_eval_one, nat.cast_one, div_one, finset.sum_singleton,
    finset.range_one, monoid_hom.coe_mk],
  rw extend_eq_char _ is_unit_one,
  convert one_mul _,
end

lemma general_bernoulli_number_one_eval {n : ℕ} :
  general_bernoulli_number (1 : dirichlet_character S 1) n = algebra_map ℚ S (bernoulli' n) :=
begin
  rw general_bernoulli_number_def, rw conductor_one nat.one_pos,
  simp only [one_pow, one_mul, nat.cast_zero, bernoulli_poly.bernoulli_poly_eval_one,
    nat.cast_one, div_one, finset.sum_singleton, finset.range_one, monoid_hom.coe_mk],
  rw extend_eq_char _ is_unit_one,
  convert one_mul _,
end

lemma finset.sum_range_mul_eq_sum_Ico {m n : ℕ} (f : ℕ → S) :
  ∑ a in finset.range (m * n), f a =
  ∑ i in finset.range n, (∑ a in finset.Ico (m * i) (m * i.succ), f a) :=
begin
  induction n with d hd,
  { simp only [finset.sum_empty, finset.range_zero, mul_zero], },
  { rw [finset.sum_range_succ, ←hd, finset.range_eq_Ico, finset.range_eq_Ico,
     finset.sum_Ico_consecutive _ (nat.zero_le _)
     (mul_le_mul (le_refl _) (nat.le_succ _) (nat.zero_le _) (nat.zero_le _))], },
end

example {a b c : ℚ} (h : a + b = c) : b = c - a := eq_sub_of_add_eq' h

theorem bernoulli_polynomial.eval_mul (m : ℕ) {k x : ℕ} (hk : k ≠ 0) (hx : 0 < x) :
  (bernoulli_poly m).eval (k * x) = k^(m - 1 : ℤ) *
  ∑ i in finset.range k, (bernoulli_poly m).eval (x + i / k) :=
begin
  apply nat.strong_induction_on m (λ n h, _),
  suffices : (((n.succ : ℚ) • bernoulli_poly n).eval (k * x)) =
    (k^(n - 1 : ℤ) * ∑ i in finset.range k, ((n.succ : ℚ) • bernoulli_poly n).eval (x + i / k)),
  { /-rw mul_eq_mul_left_iff at this, cases this,
    { rw this, },
    { exfalso, norm_cast at this, }, -/ sorry, },
  { have := bernoulli_poly.sum_bernoulli_poly n,
    rw finset.sum_range_succ at this,
    have f2 := eq_sub_of_add_eq' this,
    rw nat.choose_succ_self_right n at f2,
    rw f2,
    sorry, },


  simp at this,
--  induction m with d  hd,
  { simp only [gpow_one, bernoulli_poly.bernoulli_poly_zero, zero_sub, int.coe_nat_zero,
      finset.sum_const, polynomial.eval_one, fpow_neg, finset.card_range, nat.smul_one_eq_coe],
    rw inv_mul_cancel _,
    simp only [hk, ne.def, nat.cast_eq_zero, not_false_iff], },
  {
    sorry, },
  have f1 := bernoulli_poly.exp_bernoulli_poly' (k * x : ℚ),

--  rw ←power_series.exp_pow_eq_rescale_exp at f1,
  have f2 := geom_sum_eq _ k,
  induction x with d hd,
  simp,
  rw bernoulli_poly_def,
  /-rw polynomial.eval_finset_sum,
  simp_rw [polynomial.eval_monomial], -/
  conv_rhs { congr, skip, apply_congr, skip, rw polynomial.eval_finset_sum, },
  simp_rw [polynomial.eval_monomial],
--  conv_rhs { congr, skip, apply_congr, skip, apply_congr, skip, rw polynomial.eval_monomial, },

  sorry
end

lemma eq_sum_bernoulli_of_conductor_dvd {F : ℕ} [hF : fact (0 < F)] (m : ℕ) (h : ψ.conductor ∣ F) :
  general_bernoulli_number ψ m =
  F^(m - 1) * (∑ a in finset.range F, asso_dirichlet_character ψ a.succ *
    algebra_map ℚ S ((bernoulli_poly m).eval (a.succ / F : ℚ))) :=
begin
  cases h with k h, rw h,
  rw finset.sum_range_mul_eq_sum_Ico,
  --rw bernoulli_polynomial.eval_mul,
  sorry,
end

end general_bernoulli_number
