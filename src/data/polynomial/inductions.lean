/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Damiano Testa, Jens Wagemaker
-/
import data.nat.interval
import data.polynomial.degree.definitions
import data.polynomial.induction

/-!
# Induction on polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas dealing with different flavours of induction on polynomials.
-/

noncomputable theory
open_locale classical big_operators polynomial

open finset

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section semiring
variables [semiring R] {p q : R[X]}

/-- `div_X p` returns a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X (p : R[X]) : R[X] :=
∑ n in Ico 0 p.nat_degree, monomial n (p.coeff (n + 1))

@[simp] lemma coeff_div_X : (div_X p).coeff n = p.coeff (n+1) :=
begin
  simp only [div_X, coeff_monomial, true_and, finset_sum_coeff, not_lt,
    mem_Ico, zero_le, finset.sum_ite_eq', ite_eq_left_iff],
  intro h,
  rw coeff_eq_zero_of_nat_degree_lt (nat.lt_succ_of_le h)
end

lemma div_X_mul_X_add (p : R[X]) : div_X p * X + C (p.coeff 0) = p :=
ext $ by rintro ⟨_|_⟩; simp [coeff_C, nat.succ_ne_zero, coeff_mul_X]

@[simp] lemma div_X_C (a : R) : div_X (C a) = 0 :=
ext $ λ n, by simp [div_X, coeff_C]; simp [coeff]

lemma div_X_eq_zero_iff : div_X p = 0 ↔ p = C (p.coeff 0) :=
⟨λ h, by simpa [eq_comm, h] using div_X_mul_X_add p,
  λ h, by rw [h, div_X_C]⟩

lemma div_X_add : div_X (p + q) = div_X p + div_X q :=
ext $ by simp

lemma degree_div_X_lt (hp0 : p ≠ 0) : (div_X p).degree < p.degree :=
by haveI := nontrivial.of_polynomial_ne hp0;
calc (div_X p).degree < (div_X p * X + C (p.coeff 0)).degree :
  if h : degree p ≤ 0
  then begin
      have h' : C (p.coeff 0) ≠ 0, by rwa [← eq_C_of_degree_le_zero h],
      rw [eq_C_of_degree_le_zero h, div_X_C, degree_zero, zero_mul, zero_add],
      exact lt_of_le_of_ne bot_le (ne.symm (mt degree_eq_bot.1 $
        by simp [h'])),
    end
  else
    have hXp0 : div_X p ≠ 0,
      by simpa [div_X_eq_zero_iff, -not_le, degree_le_zero_iff] using h,
    have leading_coeff (div_X p) * leading_coeff X ≠ 0, by simpa,
    have degree (C (p.coeff 0)) < degree (div_X p * X),
      from calc degree (C (p.coeff 0)) ≤ 0 : degree_C_le
         ... < 1 : dec_trivial
         ... = degree (X : R[X]) : degree_X.symm
         ... ≤ degree (div_X p * X) :
          by rw [← zero_add (degree X), degree_mul' this];
            exact add_le_add
              (by rw [zero_le_degree_iff, ne.def, div_X_eq_zero_iff];
                exact λ h0, h (h0.symm ▸ degree_C_le))
              le_rfl,
    by rw [degree_add_eq_left_of_degree_lt this];
      exact degree_lt_degree_mul_X hXp0
... = p.degree : congr_arg _ (div_X_mul_X_add _)

/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_eliminator] noncomputable def rec_on_horner
  {M : R[X] → Sort*} : Π (p : R[X]),
  M 0 →
  (Π p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a)) →
  (Π p, p ≠ 0 → M p → M (p * X)) →
  M p
| p := λ M0 MC MX,
if hp : p = 0 then eq.rec_on hp.symm M0
else
have wf : degree (div_X p) < degree p,
  from degree_div_X_lt hp,
by rw [← div_X_mul_X_add p] at *;
  exact
  if hcp0 : coeff p 0 = 0
  then by rw [hcp0, C_0, add_zero];
    exact MX _ (λ h : div_X p = 0, by simpa [h, hcp0] using hp)
      (rec_on_horner _ M0 MC MX)
  else MC _ _ (coeff_mul_X_zero _) hcp0 (if hpX0 : div_X p = 0
    then show M (div_X p * X), by rw [hpX0, zero_mul]; exact M0
    else MX (div_X p) hpX0 (rec_on_horner _ M0 MC MX))
using_well_founded {dec_tac := tactic.assumption}

/--  A property holds for all polynomials of positive `degree` with coefficients in a semiring `R`
if it holds for
* `a * X`, with `a ∈ R`,
* `p * X`, with `p ∈ R[X]`,
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
with appropriate restrictions on each term.

See `nat_degree_ne_zero_induction_on` for a similar statement involving no explicit multiplication.
 -/
@[elab_as_eliminator] lemma degree_pos_induction_on
  {P : R[X] → Prop} (p : R[X]) (h0 : 0 < degree p)
  (hC : ∀ {a}, a ≠ 0 → P (C a * X))
  (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
  (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
rec_on_horner p
  (λ h, by rw degree_zero at h; exact absurd h dec_trivial)
  (λ p a _ _ ih h0,
    have 0 < degree p,
      from lt_of_not_ge (λ h, (not_lt_of_ge degree_C_le) $
        by rwa [eq_C_of_degree_le_zero h, ← C_add] at h0),
    hadd this (ih this))
  (λ p _ ih h0',
    if h0 : 0 < degree p
    then hX h0 (ih h0)
    else by rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at *;
      exact hC (λ h : coeff p 0 = 0,
        by simpa [h, nat.not_lt_zero] using h0'))
  h0

/--  A property holds for all polynomials of non-zero `nat_degree` with coefficients in a
semiring `R` if it holds for
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
* `p + q`, with `p, q ∈ R[X]`,
* monomials with nonzero coefficient and non-zero exponent,
with appropriate restrictions on each term.
Note that multiplication is "hidden" in the assumption on monomials, so there is no explicit
multiplication in the statement.
See `degree_pos_induction_on` for a similar statement involving more explicit multiplications.
 -/
@[elab_as_eliminator] lemma nat_degree_ne_zero_induction_on {M : R[X] → Prop}
  {f : R[X]} (f0 : f.nat_degree ≠ 0) (h_C_add : ∀ {a p}, M p → M (C a + p))
  (h_add : ∀ {p q}, M p → M q → M (p + q))
  (h_monomial : ∀ {n : ℕ} {a : R}, a ≠ 0 → n ≠ 0 → M (monomial n a)) :
  M f :=
suffices f.nat_degree = 0 ∨ M f, from or.dcases_on this (λ h, (f0 h).elim) id,
begin
  apply f.induction_on,
  { exact λ a, or.inl (nat_degree_C _) },
  { rintros p q (hp | hp) (hq | hq),
    { refine or.inl _,
      rw [eq_C_of_nat_degree_eq_zero hp, eq_C_of_nat_degree_eq_zero hq, ← C_add, nat_degree_C] },
    { refine or.inr _,
      rw [eq_C_of_nat_degree_eq_zero hp],
      exact h_C_add hq },
    { refine or.inr _,
      rw [eq_C_of_nat_degree_eq_zero hq, add_comm],
      exact h_C_add hp },
    { exact or.inr (h_add hp hq) } },
  { intros n a hi,
    by_cases a0 : a = 0,
    { exact or.inl (by rw [a0, C_0, zero_mul, nat_degree_zero]) },
    { refine or.inr _,
      rw C_mul_X_pow_eq_monomial,
      exact h_monomial a0 n.succ_ne_zero } }
end

end semiring

end polynomial
