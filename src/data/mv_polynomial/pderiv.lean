/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/

import data.mv_polynomial.variables
import data.mv_polynomial.derivation

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderiv i p` : the partial derivative of `p` with respect to `i`, as a bundled
  derivation of `mv_polynomial σ R`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/

noncomputable theory

universes u v

namespace mv_polynomial


open set function finsupp add_monoid_algebra
open_locale classical big_operators

variables {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

section pderiv

variables {R} [comm_semiring R]

/-- `pderiv i p` is the partial derivative of `p` with respect to `i` -/
def pderiv (i : σ) : derivation R (mv_polynomial σ R) (mv_polynomial σ R) :=
mk_derivation R $ pi.single i 1

@[simp] lemma pderiv_monomial {i : σ} :
  pderiv i (monomial s a) = monomial (s - single i 1) (a * (s i)) :=
begin
  simp only [pderiv, mk_derivation_monomial, finsupp.smul_sum, smul_eq_mul,
    ← smul_mul_assoc, ← (monomial _).map_smul],
  refine (finset.sum_eq_single i (λ j hj hne, _) (λ hi, _)).trans _,
  { simp [pi.single_eq_of_ne hne] },
  { rw [finsupp.not_mem_support_iff] at hi, simp [hi] },
  { simp }
end

lemma pderiv_C {i : σ} : pderiv i (C a) = 0 := derivation_C _ _

lemma pderiv_one {i : σ} : pderiv i (1 : mv_polynomial σ R) = 0 := pderiv_C

@[simp] lemma pderiv_X [d : decidable_eq σ] (i j : σ) :
  pderiv i (X j : mv_polynomial σ R) = @pi.single σ _ d _ i 1 j :=
(mk_derivation_X _ _ _).trans (by congr)

@[simp] lemma pderiv_X_self (i : σ) : pderiv i (X i : mv_polynomial σ R) = 1 := by simp

@[simp] lemma pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : mv_polynomial σ R) = 0 :=
by simp [h]

lemma pderiv_eq_zero_of_not_mem_vars {i : σ} {f : mv_polynomial σ R} (h : i ∉ f.vars) :
  pderiv i f = 0 :=
derivation_eq_zero_of_forall_mem_vars $ λ j hj, pderiv_X_of_ne $ ne_of_mem_of_not_mem hj h

lemma pderiv_monomial_single {i : σ} {n : ℕ} :
  pderiv i (monomial (single i n) a) = monomial (single i (n-1)) (a * n) :=
by simp

lemma pderiv_mul {i : σ} {f g : mv_polynomial σ R} :
  pderiv i (f * g) = pderiv i f * g + f * pderiv i g :=
by simp only [(pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]

@[simp] lemma pderiv_C_mul {f : mv_polynomial σ R} {i : σ} :
  pderiv i (C a * f) = C a * pderiv i f :=
(derivation_C_mul _ _ _).trans C_mul'.symm

end pderiv

end mv_polynomial
