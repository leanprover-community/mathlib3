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

example (a : ℕ) : a.succ - a = 1 := norm_num.sub_nat_pos (nat.succ a) a 1 rfl

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

example (f : ℕ × ℕ → ℚ) (a b : ℕ) :
  (∑ i in finset.range a, (∑ j in finset.range b, (f (i, j)))) =
    ∑ i in finset.range b, (∑ j in finset.range a, f (i, j)) := by {simp}

example (a b c : ℚ) (hc : c ≠ 0) : c * (a / (b * c)) = a / b := sorry

lemma eq_sum_bernoulli_of_conductor_dvd {F : ℕ} [hF : fact (0 < F)] (m : ℕ) (h : ψ.conductor ∣ F) :
  general_bernoulli_number ψ m =
  F^(m - 1) * (∑ a in finset.range F, asso_dirichlet_character ψ a.succ *
    algebra_map ℚ S ((bernoulli_poly m).eval (a.succ / F : ℚ))) :=
begin
  cases h with k h, rw h,
  rw finset.sum_range_mul_eq_sum_Ico,
  simp_rw [finset.sum_Ico_eq_sum_range],
  simp_rw [←nat.mul_sub_left_distrib],
  simp_rw [norm_num.sub_nat_pos (nat.succ _) _ 1 rfl],
  simp_rw [mul_one],
  rw general_bernoulli_number_def,
  have hk1 : k ≠ 0, sorry,
  have hk2 : (k : ℚ) ≠ 0, sorry,
  conv_lhs { congr, skip, apply_congr, skip,
    rw [←mul_div_mul_left _ _ hk2, ←mul_div_assoc', bernoulli_poly.eval_mul _ hk1,
    (algebra_map _ _).map_mul, (algebra_map _ _).map_sum, ←mul_assoc,
    mul_comm ((asso_dirichlet_character ψ) ↑(x.succ)) _, mul_assoc, finset.mul_sum], },
  rw [←finset.mul_sum, ←mul_assoc],
  apply congr_arg2,
  sorry,
  { rw finset.sum_comm,
    apply finset.sum_congr rfl (λ i hi, _),
    apply finset.sum_congr rfl (λ j hj, _),
    apply congr_arg2,
    sorry,
    { apply congr_arg, congr, sorry, }, },
end

end general_bernoulli_number
