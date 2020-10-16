/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.polynomial.degree.basic

/-!
# Induction principles for polynomials, based on degree

## Main results
* `induction_on_degree` allows proving a result for all polynomials by induction on degree.
-/

namespace polynomial

variables {R : Type*} [semiring R]

@[elab_as_eliminator] protected lemma induction_on_degree
  {M : polynomial R → Prop} (p : polynomial R)
  (h_0 : M 0)
  (h_degree : ∀ (p : polynomial R), p ≠ 0 → (∀ q : polynomial R, q.degree < p.degree → M q) → M p) :
  M p :=
begin
  suffices h : ∀ (n : ℕ) (q : polynomial R), q.nat_degree ≤ n → M q,
  { exact h p.nat_degree p (le_refl _) },
  intro n,
  induction n with n ih; intros p h,
  { by_cases p0 : p = 0,
    { rw p0,
      apply h_0 },
    apply h_degree p p0 (λ q hq, _),
    rw [nat.le_zero_iff, ← degree_eq_iff_nat_degree_eq p0] at h,
    rw [h, with_bot.coe_zero, nat.with_bot.lt_zero_iff, degree_eq_bot] at hq,
    rw hq,
    apply h_0 },
  { by_cases p0 : p = 0,
    { rw p0,
      apply h_0 },
    apply h_degree p p0,
    { intros q qp,
      by_cases q0 : q = 0,
      { rw q0,
        apply h_0 },
      rw [degree_eq_nat_degree p0, degree_eq_nat_degree q0, with_bot.coe_lt_coe] at qp,
      apply ih q (nat.lt_succ_iff.1 (lt_of_lt_of_le qp h)) } }
end

end polynomial
