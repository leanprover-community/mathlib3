/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.degree.basic
import data.polynomial.degree
import data.polynomial.degree.trailing_degree

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

noncomputable theory
open_locale classical

open polynomial finsupp finset

namespace polynomial

variables {R : Type*} [semiring R] {f : polynomial R}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def erase_lead (f : polynomial R) : polynomial R :=
finsupp.erase f.nat_degree f

section erase_lead

lemma erase_lead_support (f : polynomial R) :
  f.erase_lead.support = f.support.erase f.nat_degree :=
-- `rfl` fails because LHS uses `nat.decidable_eq` but RHS is classical.
by convert rfl

lemma erase_lead_coeff (i : ℕ) :
  f.erase_lead.coeff i = if i = f.nat_degree then 0 else f.coeff i :=
-- `rfl` fails because LHS uses `nat.decidable_eq` but RHS is classical.
by convert rfl

@[simp] lemma erase_lead_coeff_nat_degree : f.erase_lead.coeff f.nat_degree = 0 :=
finsupp.erase_same

lemma erase_lead_coeff_of_ne (i : ℕ) (hi : i ≠ f.nat_degree) :
  f.erase_lead.coeff i = f.coeff i :=
finsupp.erase_ne hi

@[simp] lemma erase_lead_zero : erase_lead (0 : polynomial R) = 0 :=
finsupp.erase_zero _

@[simp] lemma erase_lead_add_monomial_nat_degree_leading_coeff (f : polynomial R) :
  f.erase_lead + monomial f.nat_degree f.leading_coeff = f :=
begin
  ext i,
  simp only [erase_lead_coeff, coeff_monomial, coeff_add, @eq_comm _ _ i],
  split_ifs with h,
  { subst i, simp only [leading_coeff, zero_add] },
  { exact add_zero _ }
end

@[simp] lemma erase_lead_add_C_mul_X_pow (f : polynomial R) :
  f.erase_lead + (C f.leading_coeff) * X ^ f.nat_degree = f :=
by rw [C_mul_X_pow_eq_monomial, erase_lead_add_monomial_nat_degree_leading_coeff]

@[simp] lemma self_sub_monomial_nat_degree_leading_coeff {R : Type*} [ring R] (f : polynomial R) :
  f - monomial f.nat_degree f.leading_coeff = f.erase_lead :=
(eq_sub_iff_add_eq.mpr (erase_lead_add_monomial_nat_degree_leading_coeff f)).symm

@[simp] lemma self_sub_C_mul_X_pow {R : Type*} [ring R] (f : polynomial R) :
  f - (C f.leading_coeff) * X ^ f.nat_degree = f.erase_lead :=
by rw [C_mul_X_pow_eq_monomial, self_sub_monomial_nat_degree_leading_coeff]

lemma erase_lead_ne_zero (f0 : 2 ≤ f.support.card) : erase_lead f ≠ 0 :=
begin
  rw [ne.def, ← finsupp.card_support_eq_zero, erase_lead_support],
  exact (zero_lt_one.trans_le $ (nat.sub_le_sub_right f0 1).trans
    finset.pred_card_le_card_erase).ne.symm
end

@[simp] lemma nat_degree_not_mem_erase_lead_support : f.nat_degree ∉ (erase_lead f).support :=
by convert not_mem_erase _ _

lemma ne_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (erase_lead f).support) :
  a ≠ f.nat_degree :=
by { rintro rfl, exact nat_degree_not_mem_erase_lead_support h }

lemma erase_lead_support_card_lt (h : f ≠ 0) : (erase_lead f).support.card < f.support.card :=
begin
  rw erase_lead_support,
  exact card_lt_card (erase_ssubset $ nat_degree_mem_support_of_nonzero h)
end

@[simp] lemma erase_lead_monomial (i : ℕ) (r : R) :
  erase_lead (monomial i r) = 0 :=
begin
  by_cases hr : r = 0,
  { subst r, simp only [monomial_zero_right, erase_lead_zero] },
  { rw [erase_lead, nat_degree_monomial _ _ hr, monomial, erase_single] }
end

@[simp] lemma erase_lead_C (r : R) : erase_lead (C r) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X : erase_lead (X : polynomial R) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X_pow (n : ℕ) : erase_lead (X ^ n : polynomial R) = 0 :=
by rw [X_pow_eq_monomial, erase_lead_monomial]

@[simp] lemma erase_lead_C_mul_X_pow (r : R) (n : ℕ) : erase_lead (C r * X ^ n) = 0 :=
by rw [C_mul_X_pow_eq_monomial, erase_lead_monomial]

lemma erase_lead_degree_le : (erase_lead f).degree ≤ f.degree :=
begin
  rw degree_le_iff_coeff_zero,
  intros i hi,
  rw erase_lead_coeff,
  split_ifs with h, { refl },
  apply coeff_eq_zero_of_degree_lt hi
end

lemma erase_lead_nat_degree_le : (erase_lead f).nat_degree ≤ f.nat_degree :=
nat_degree_le_nat_degree erase_lead_degree_le

lemma erase_lead_nat_degree_lt (f0 : 2 ≤ f.support.card) :
  (erase_lead f).nat_degree < f.nat_degree :=
lt_of_le_of_ne erase_lead_nat_degree_le $ ne_nat_degree_of_mem_erase_lead_support $
  nat_degree_mem_support_of_nonzero $ erase_lead_ne_zero f0

lemma erase_lead_nat_degree_lt_or_erase_lead_eq_zero (f : polynomial R) :
  (erase_lead f).nat_degree < f.nat_degree ∨ f.erase_lead = 0 :=
begin
  by_cases h : f.support.card ≤ 1,
  { right,
    rw ← C_mul_X_pow_eq_self h,
    simp },
  { left,
    apply erase_lead_nat_degree_lt (lt_of_not_ge h) }
end

end erase_lead

end polynomial
