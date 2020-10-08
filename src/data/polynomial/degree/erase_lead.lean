/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.degree.basic
import data.polynomial.degree.trailing_degree

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

open polynomial finsupp finset

namespace polynomial

variables {R : Type*} [semiring R] {f : polynomial R}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def erase_lead (f : polynomial R) : polynomial R :=
 ⟨ f.support \ singleton f.nat_degree , λ a : ℕ , ite (a = f.nat_degree) 0 f.coeff a , λ a , begin
  simp only [mem_sdiff, mem_support_iff, ne.def, mem_singleton],
  split_ifs with h,
  { simp only [not_and, pi.zero_apply, not_not, eq_self_iff_true, not_true, iff_false],
    intros a_1,
    assumption, },
  { split,
  { rw and_imp,
    intros a1 a2,
    assumption, },
  { intros a1,
    exact ⟨ a1 , h ⟩, }, },
end ⟩

namespace erase_lead

lemma support (f : polynomial R) :
 (f.erase_lead).support = f.support \ singleton f.nat_degree :=
rfl

@[simp] lemma coeff_nat_degree : f.erase_lead.coeff f.nat_degree = 0 :=
begin
  unfold erase_lead,
  simp only [coeff_mk, if_true, pi.zero_apply, eq_self_iff_true],
end

@[simp] lemma coeff_eq_coeff_of_ne {a : ℕ} (h : a ≠ f.nat_degree) :
 f.erase_lead.coeff a = f.coeff a :=
begin
  unfold erase_lead,
  rw coeff_mk,
  split_ifs,
  { exfalso,
    solve_by_elim, },
  { refl, },
end

lemma erase_lead_add_C_mul_X_pow (f : polynomial R) :
  f.erase_lead + (C f.leading_coeff) * X^f.nat_degree = f :=
begin
  ext1,
  by_cases nm : n = f.nat_degree,
  { rw [nm, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_nat_degree, zero_add],
    refl, },
  { rw [coeff_add, coeff_eq_coeff_of_ne nm, coeff_C_mul_X],
    split_ifs,
    rw add_zero (f.coeff n), },
end

@[simp] lemma sum_leading_C_mul_X_pow_ring {S : Type*} [ring S] (g : polynomial S)
 : g.erase_lead = g - (C g.leading_coeff) * X^g.nat_degree :=
eq_sub_iff_add_eq.mpr (sum_leading_C_mul_X_pow g).symm

lemma nonzero_of_large_support (f0 : 2 ≤ f.support.card) : ¬ (erase_lead f) = 0 :=
begin
  have fn0 : f ≠ 0,
  { rw [ne.def, ← support_eq_empty],
    intro a,
    rw [a, card_empty] at f0,
    exact nat.not_succ_le_zero 1 f0, },
  rw [← support_eq_empty],
  apply @ne_empty_of_mem _ (nat_trailing_degree f),
  rw [mem_support_iff_coeff_ne_zero, coeff_eq_coeff_of_ne, ← mem_support_iff_coeff_ne_zero],
  { exact nat_trailing_degree_mem_support_of_nonzero fn0, },
  { rw [nat_degree_eq_support_max' fn0, nat_trailing_degree_eq_support_min' fn0],
    exact ne_of_lt (finset.min'_lt_max'_of_card _ f0), },
end

@[simp] lemma support_ne : f.nat_degree ∉ (erase_lead f).support :=
begin
  rw [support, mem_sdiff, mem_singleton, eq_self_iff_true, not_true, and_false, not_false_iff],
  trivial,
end

@[simp] lemma ne_nat_degree_of_mem_support {a : ℕ} :
 a ∈ (erase_lead f).support → ¬ a = f.nat_degree :=
begin
  rw [support, mem_sdiff, mem_singleton, and_imp, imp_self, forall_true_iff],
  trivial,
end

lemma mem_of_mem_diff {a : ℕ} : a ∈ (f.support \ {f.nat_degree}) ↔ a ∈ (erase_lead f).support :=
by rw support

lemma nat_degree (f0 : 2 ≤ f.support.card) : (erase_lead f).nat_degree < f.nat_degree :=
begin
  rw nat_degree_eq_support_max' (nonzero_of_large_support f0),
  apply nat.lt_of_le_and_ne _
   (ne_nat_degree_of_mem_support ((erase_lead f).support.max'_mem (nonempty_support_iff.mpr _))),
  simp_rw support f,
  apply max'_le,
  intros y hy,
  apply le_nat_degree_of_ne_zero,
  rw mem_sdiff at hy,
  exact (mem_support_iff_coeff_ne_zero.mp hy.1),
end

lemma support_card_lt (h : f ≠ 0) : (erase_lead f).support.card < f.support.card :=
begin
  apply card_lt_card,
  rw [support, ssubset_iff_of_subset (f.support.sdiff_subset {f.nat_degree})],
  use f.nat_degree,
  rw [← mem_sdiff, sdiff_sdiff_self_left, inter_singleton_of_mem, mem_singleton],
  rw mem_support_iff_coeff_ne_zero,
  exact (not_congr leading_coeff_eq_zero).mpr h,
end

lemma add_cancel {a b : R} {h : a=0} : a+b=b :=
by rw [h, zero_add]

lemma C_mul_X_pow_of_card_support_le_one (h : f.support.card ≤ 1) :
 f = C f.leading_coeff * X^f.nat_degree :=
begin
  by_cases f0 : f = 0,
  { ext1,
    rw [f0, leading_coeff_zero, C_0, zero_mul], },
  { conv_lhs {rw sum_leading_C_mul_X_pow f},
    apply add_cancel,
    rw [← support_eq_empty, ← card_eq_zero],
    apply nat.eq_zero_of_le_zero (nat.lt_succ_iff.mp _),
    convert support_card_lt f0,
    apply le_antisymm _ h,
    exact card_le_of_subset (singleton_subset_iff.mpr (nat_degree_mem_support_of_nonzero f0)), },
end

lemma C_mul_X_pow_eq_zero {r : R} {n : ℕ} : erase_lead (C r * X^n) = 0 :=
begin
  rw [← support_eq_empty, support, sdiff_eq_empty_iff_subset],
  by_cases r0 : r=0,
  { rw [r0, C_0, zero_mul, polynomial.support_zero],
    exact empty_subset _, },
  { convert support_C_mul_X_pow r n,
    rw nat_degree_C_mul_X_pow_of_nonzero n r0, },
end

lemma nat_degree_le : (erase_lead f).nat_degree ≤ f.nat_degree :=
begin
  by_cases su : f.support.card ≤ 1,
  { rw [C_mul_X_pow_of_card_support_le_one su, C_mul_X_pow_eq_zero, nat_degree_zero],
    exact zero_le _, },
  { apply le_of_lt,
    exact nat_degree (nat.succ_le_iff.mpr (not_le.mp su)), },
end

end erase_lead
end polynomial
