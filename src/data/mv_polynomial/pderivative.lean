/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import data.mv_polynomial.variables
import tactic.ring

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderivative i p` : the partial derivative of `p` with respect to `i`.

## Notation

As in other polynomial files we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `α : Type*` `[comm_ring α]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : α`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section pderivative

variables {α} [comm_semiring α]

/-- `pderivative i p` is the partial derivative of `p` with respect to `i` -/
def pderivative (i : σ) (p : mv_polynomial σ α) : mv_polynomial σ α :=
p.sum (λ A B, monomial (A - single i 1) (B * (A i)))

@[simp]
lemma pderivative_add {i : σ} {f g : mv_polynomial σ α} :
  pderivative i (f + g) = pderivative i f + pderivative i g :=
begin
  refine sum_add_index _ _,
  { simp },
  simp [add_mul],
end

@[simp]
lemma pderivative_monomial {i : σ} :
  pderivative i (monomial s a) = monomial (s - single i 1) (a * (s i)) :=
by simp [pderivative]

@[simp]
lemma pderivative_C {i : σ} : pderivative i (C a) = 0 :=
suffices pderivative i (monomial 0 a) = 0, by simpa,
by simp

@[simp]
lemma pderivative_zero {i : σ} : pderivative i (0 : mv_polynomial σ α) = 0 :=
suffices pderivative i (C 0 : mv_polynomial σ α) = 0, by simpa,
show pderivative i (C 0 : mv_polynomial σ α) = 0, from pderivative_C

section
variables (α)

/-- `pderivative : S → mv_polynomial σ α → mv_polynomial σ α` as an `add_monoid_hom`  -/
def pderivative.add_monoid_hom (i : σ) : mv_polynomial σ α →+ mv_polynomial σ α :=
{ to_fun := pderivative i,
  map_zero' := pderivative_zero,
  map_add' := λ x y, pderivative_add, }

@[simp]
lemma pderivative.add_monoid_hom_apply (i : σ) (p : mv_polynomial σ α) :
  (pderivative.add_monoid_hom α i) p = pderivative i p :=
rfl
end

lemma pderivative_eq_zero_of_not_mem_vars {i : σ} {f : mv_polynomial σ α} (h : i ∉ f.vars) :
  pderivative i f = 0 :=
begin
  change (pderivative.add_monoid_hom α i) f = 0,
  rw [f.as_sum, add_monoid_hom.map_sum],
  apply finset.sum_eq_zero,
  intros,
  simp [mem_support_not_mem_vars_zero H h],
end

lemma pderivative_monomial_single {i : σ} {n : ℕ} :
  pderivative i (monomial (single i n) a) = monomial (single i (n-1)) (a * n) :=
by simp

private lemma monomial_sub_single_one_add {i : σ} {s' : σ →₀ ℕ} :
  monomial (s - single i 1 + s') (a * (s i) * a') =
    monomial (s + s' - single i 1) (a * (s i) * a') :=
by by_cases h : s i = 0; simp [h, sub_single_one_add]

private lemma monomial_add_sub_single_one {i : σ} {s' : σ →₀ ℕ} :
  monomial (s + (s' - single i 1)) (a * (a' * (s' i))) =
    monomial (s + s' - single i 1) (a * (a' * (s' i))) :=
by by_cases h : s' i = 0; simp [h, add_sub_single_one]

lemma pderivative_monomial_mul {i : σ} {s' : σ →₀ ℕ} :
  pderivative i (monomial s a * monomial s' a') =
    pderivative i (monomial s a) * monomial s' a' + monomial s a * pderivative i (monomial s' a') :=
begin
  simp [monomial_sub_single_one_add, monomial_add_sub_single_one],
  congr,
  ring,
end

@[simp]
lemma pderivative_mul {i : σ} {f g : mv_polynomial σ α} :
  pderivative i (f * g) = pderivative i f * g + f * pderivative i g :=
begin
  apply induction_on' f,
  { apply induction_on' g,
    { intros u r u' r', exact pderivative_monomial_mul },
    { intros p q hp hq u r,
      rw [mul_add, pderivative_add, hp, hq, mul_add, pderivative_add],
      ring } },
  { intros p q hp hq,
    simp [add_mul, hp, hq],
    ring, }
end

@[simp]
lemma pderivative_C_mul {f : mv_polynomial σ α} {i : σ} :
  pderivative i (C a * f) = C a * pderivative i f :=
by rw [pderivative_mul, pderivative_C, zero_mul, zero_add]

end pderivative

end mv_polynomial
