/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.degree.definitions

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

noncomputable theory
open_locale classical polynomial

open polynomial finset

namespace polynomial

variables {R : Type*} [semiring R] {f : R[X]}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def erase_lead (f : R[X]) : R[X] :=
polynomial.erase f.nat_degree f

section erase_lead

lemma erase_lead_support (f : R[X]) :
  f.erase_lead.support = f.support.erase f.nat_degree :=
by simp only [erase_lead, support_erase]

lemma erase_lead_coeff (i : ℕ) :
  f.erase_lead.coeff i = if i = f.nat_degree then 0 else f.coeff i :=
by simp only [erase_lead, coeff_erase]

@[simp] lemma erase_lead_coeff_nat_degree : f.erase_lead.coeff f.nat_degree = 0 :=
by simp [erase_lead_coeff]

lemma erase_lead_coeff_of_ne (i : ℕ) (hi : i ≠ f.nat_degree) :
  f.erase_lead.coeff i = f.coeff i :=
by simp [erase_lead_coeff, hi]

@[simp] lemma erase_lead_zero : erase_lead (0 : R[X]) = 0 :=
by simp only [erase_lead, erase_zero]

@[simp] lemma erase_lead_add_monomial_nat_degree_leading_coeff (f : R[X]) :
  f.erase_lead + monomial f.nat_degree f.leading_coeff = f :=
begin
  ext i,
  simp only [erase_lead_coeff, coeff_monomial, coeff_add, @eq_comm _ _ i],
  split_ifs with h,
  { subst i, simp only [leading_coeff, zero_add] },
  { exact add_zero _ }
end

@[simp] lemma erase_lead_add_C_mul_X_pow (f : R[X]) :
  f.erase_lead + (C f.leading_coeff) * X ^ f.nat_degree = f :=
by rw [C_mul_X_pow_eq_monomial, erase_lead_add_monomial_nat_degree_leading_coeff]

@[simp] lemma self_sub_monomial_nat_degree_leading_coeff {R : Type*} [ring R] (f : R[X]) :
  f - monomial f.nat_degree f.leading_coeff = f.erase_lead :=
(eq_sub_iff_add_eq.mpr (erase_lead_add_monomial_nat_degree_leading_coeff f)).symm

@[simp] lemma self_sub_C_mul_X_pow {R : Type*} [ring R] (f : R[X]) :
  f - (C f.leading_coeff) * X ^ f.nat_degree = f.erase_lead :=
by rw [C_mul_X_pow_eq_monomial, self_sub_monomial_nat_degree_leading_coeff]

lemma erase_lead_ne_zero (f0 : 2 ≤ f.support.card) : erase_lead f ≠ 0 :=
begin
  rw [ne.def, ← card_support_eq_zero, erase_lead_support],
  exact (zero_lt_one.trans_le $ (tsub_le_tsub_right f0 1).trans
    finset.pred_card_le_card_erase).ne.symm
end

@[simp] lemma nat_degree_not_mem_erase_lead_support : f.nat_degree ∉ (erase_lead f).support :=
by simp [not_mem_support_iff]

lemma ne_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (erase_lead f).support) :
  a ≠ f.nat_degree :=
by { rintro rfl, exact nat_degree_not_mem_erase_lead_support h }

lemma erase_lead_support_card_lt (h : f ≠ 0) : (erase_lead f).support.card < f.support.card :=
begin
  rw erase_lead_support,
  exact card_lt_card (erase_ssubset $ nat_degree_mem_support_of_nonzero h)
end

lemma erase_lead_card_support {c : ℕ} (fc : f.support.card = c) :
  f.erase_lead.support.card = c - 1 :=
begin
  by_cases f0 : f = 0,
  { rw [← fc, f0, erase_lead_zero, support_zero, card_empty] },
  { rw [erase_lead_support, card_erase_of_mem (nat_degree_mem_support_of_nonzero f0), fc],
    exact c.pred_eq_sub_one },
end

lemma erase_lead_card_support' {c : ℕ} (fc : f.support.card = c + 1) :
  f.erase_lead.support.card = c :=
erase_lead_card_support fc

@[simp] lemma erase_lead_monomial (i : ℕ) (r : R) :
  erase_lead (monomial i r) = 0 :=
begin
  by_cases hr : r = 0,
  { subst r, simp only [monomial_zero_right, erase_lead_zero] },
  { rw [erase_lead, nat_degree_monomial, if_neg hr, erase_monomial] }
end

@[simp] lemma erase_lead_C (r : R) : erase_lead (C r) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X : erase_lead (X : R[X]) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X_pow (n : ℕ) : erase_lead (X ^ n : R[X]) = 0 :=
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

lemma erase_lead_nat_degree_lt_or_erase_lead_eq_zero (f : R[X]) :
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

/-- An induction lemma for polynomials. It takes a natural number `N` as a parameter, that is
required to be at least as big as the `nat_degree` of the polynomial.  This is useful to prove
results where you want to change each term in a polynomial to something else depending on the
`nat_degree` of the polynomial itself and not on the specific `nat_degree` of each term. -/
lemma induction_with_nat_degree_le (P : R[X] → Prop) (N : ℕ)
  (P_0 : P 0)
  (P_C_mul_pow : ∀ n : ℕ, ∀ r : R, r ≠ 0 → n ≤ N → P (C r * X ^ n))
  (P_C_add : ∀ f g : R[X], f.nat_degree < g.nat_degree →
    g.nat_degree ≤ N → P f → P g → P (f + g)) :
  ∀ f : R[X], f.nat_degree ≤ N → P f :=
begin
  intros f df,
  generalize' hd : card f.support = c,
  revert f,
  induction c with c hc,
  { assume f df f0,
    convert P_0,
    simpa only [support_eq_empty, card_eq_zero] using f0 },
  { intros f df f0,
    rw [← erase_lead_add_C_mul_X_pow f],
    cases c,
    { convert P_C_mul_pow f.nat_degree f.leading_coeff _ df,
      { convert zero_add _,
        rw [← card_support_eq_zero, erase_lead_card_support f0] },
      { rw [leading_coeff_ne_zero, ne.def, ← card_support_eq_zero, f0],
        exact zero_ne_one.symm } },
    refine P_C_add f.erase_lead _ _ _ _ _,
    { refine (erase_lead_nat_degree_lt _).trans_le (le_of_eq _),
      { exact (nat.succ_le_succ (nat.succ_le_succ (nat.zero_le _))).trans f0.ge },
      { rw [nat_degree_C_mul_X_pow _ _ (leading_coeff_ne_zero.mpr _)],
        rintro rfl,
        simpa using f0 } },
    { exact (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree).trans df },
    { exact hc _ (erase_lead_nat_degree_le.trans df) (erase_lead_card_support f0) },
    { refine P_C_mul_pow _ _ _ df,
      rw [ne.def, leading_coeff_eq_zero, ← card_support_eq_zero, f0],
      exact nat.succ_ne_zero _ } }
end

/-- Let `φ : R[x] → S[x]` be an additive map, `k : ℕ` a bound, and `fu : ℕ → ℕ` a
"sufficiently monotone" map.  Assume also that
* `φ` maps to `0` all monomials of degree less than `k`,
* `φ` maps each monomial `m` in `R[x]` to a polynomial `φ m` of degree `fu (deg m)`.
Then, `φ` maps each polynomial `p` in `R[x]` to a polynomial of degree `fu (deg p)`. -/
lemma mono_map_nat_degree_eq {S F : Type*} [semiring S]
  [add_monoid_hom_class F R[X] S[X]] {φ : F}
  {p : R[X]} (k : ℕ)
  (fu : ℕ → ℕ) (fu0 : ∀ {n}, n ≤ k → fu n = 0) (fc : ∀ {n m}, k ≤ n → n < m → fu n < fu m)
  (φ_k : ∀ {f : R[X]}, f.nat_degree < k → φ f = 0)
  (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).nat_degree = fu n) :
  (φ p).nat_degree = fu p.nat_degree :=
begin
  refine induction_with_nat_degree_le (λ p, _ = fu _) p.nat_degree (by simp [fu0]) _ _ _ rfl.le,
  { intros n r r0 np,
    rw [nat_degree_C_mul_X_pow _ _ r0, ← monomial_eq_C_mul_X, φ_mon_nat _ _ r0] },
  { intros f g fg gp fk gk,
    rw [nat_degree_add_eq_right_of_nat_degree_lt fg, _root_.map_add],
    by_cases FG : k ≤ f.nat_degree,
    { rw [nat_degree_add_eq_right_of_nat_degree_lt, gk],
      rw [fk, gk],
      exact fc FG fg },
    { cases k,
      { exact (FG (nat.zero_le _)).elim },
      { rwa [φ_k (not_le.mp FG), zero_add] } } }
end

lemma map_nat_degree_eq_sub {S F : Type*} [semiring S]
  [add_monoid_hom_class F R[X] S[X]] {φ : F}
  {p : R[X]} {k : ℕ}
  (φ_k : ∀ f : R[X], f.nat_degree < k → φ f = 0)
  (φ_mon : ∀ n c, c ≠ 0 → (φ (monomial n c)).nat_degree = n - k) :
  (φ p).nat_degree = p.nat_degree - k :=
mono_map_nat_degree_eq k (λ j, j - k) (by simp) (λ m n h, (tsub_lt_tsub_iff_right h).mpr) φ_k φ_mon

lemma map_nat_degree_eq_nat_degree {S F : Type*} [semiring S]
  [add_monoid_hom_class F R[X] S[X]] {φ : F} (p)
  (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).nat_degree = n) :
  (φ p).nat_degree = p.nat_degree :=
(map_nat_degree_eq_sub (λ f h, (nat.not_lt_zero _ h).elim) (by simpa)).trans p.nat_degree.sub_zero

end polynomial
