/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro, Shing Tak Lam
-/

import data.mv_polynomial.variables

/-!
# Partial derivatives of polynomials

This file defines the notion of the formal *partial derivative* of a polynomial,
the derivative with respect to a single variable.
This derivative is not connected to the notion of derivative from analysis.
It is based purely on the polynomial exponents and coefficients.

## Main declarations

* `mv_polynomial.pderivative`: the partial derivative of a multivariate polynomial

## Notation

As in other polynomial files we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

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

variables {R : Type} [comm_ring R]
variable {S : Type}

/-- `pderivative v p` is the partial derivative of `p` with respect to `v` -/
def pderivative (v : S) (p : mv_polynomial S R) : mv_polynomial S R :=
p.sum (λ A B, monomial (A - single v 1) (B * (A v)))

@[simp]
lemma pderivative_add {v : S} {f g : mv_polynomial S R} :
  pderivative v (f + g) = pderivative v f + pderivative v g :=
begin
  refine sum_add_index _ _,
  { simp },
  simp [add_mul],
end

@[simp]
lemma pderivative_monomial {v : S} {u : S →₀ ℕ} {a : R} :
  pderivative v (monomial u a) = monomial (u - single v 1) (a * (u v)) :=
by simp [pderivative]

@[simp]
lemma pderivative_C {v : S} {a : R} : pderivative v (C a) = 0 :=
suffices pderivative v (monomial 0 a) = 0, by simpa,
by simp

@[simp]
lemma pderivative_zero {v : S} : pderivative v (0 : mv_polynomial S R) = 0 :=
suffices pderivative v (C 0 : mv_polynomial S R) = 0, by simpa,
show pderivative v (C 0 : mv_polynomial S R) = 0, from pderivative_C

section
variables (R)

/-- `pderivative : S → mv_polynomial S R → mv_polynomial S R` as an `add_monoid_hom`  -/
def pderivative.add_monoid_hom (v : S) : mv_polynomial S R →+ mv_polynomial S R :=
{ to_fun := pderivative v,
  map_zero' := pderivative_zero,
  map_add' := λ x y, pderivative_add, }

@[simp]
lemma pderivative.add_monoid_hom_apply (v : S) (p : mv_polynomial S R) :
  (pderivative.add_monoid_hom R v) p = pderivative v p :=
rfl
end

lemma pderivative_eq_zero_of_not_mem_vars {v : S} {f : mv_polynomial S R} (h : v ∉ f.vars) :
  pderivative v f = 0 :=
begin
  change (pderivative.add_monoid_hom R v) f = 0,
  rw [f.as_sum, add_monoid_hom.map_sum],
  apply finset.sum_eq_zero,
  intros,
  simp [mem_support_not_mem_vars_zero H h],
end

lemma pderivative_monomial_single {a : R} {v : S} {n : ℕ} :
  pderivative v (monomial (single v n) a) = monomial (single v (n-1)) (a * n) :=
by simp

private lemma monomial_sub_single_one_add {v : S} {u u' : S →₀ ℕ} {r r' : R} :
  monomial (u - single v 1 + u') (r * (u v) * r') =
    monomial (u + u' - single v 1) (r * (u v) * r') :=
by by_cases h : u v = 0; simp [h, sub_single_one_add]

private lemma monomial_add_sub_single_one {v : S} {u u' : S →₀ ℕ} {r r' : R} :
  monomial (u + (u' - single v 1)) (r * (r' * (u' v))) =
    monomial (u + u' - single v 1) (r * (r' * (u' v))) :=
by by_cases h : u' v = 0; simp [h, add_sub_single_one]

lemma pderivative_monomial_mul {v : S} {u u' : S →₀ ℕ} {r r' : R} :
  pderivative v (monomial u r * monomial u' r') =
    pderivative v (monomial u r) * monomial u' r' + monomial u r * pderivative v (monomial u' r') :=
begin
  simp [monomial_sub_single_one_add, monomial_add_sub_single_one],
  congr,
  ring,
end

@[simp]
lemma pderivative_mul {v : S} {f g : mv_polynomial S R} :
  pderivative v (f * g) = pderivative v f * g + f * pderivative v g :=
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
lemma pderivative_C_mul {a : R} {f : mv_polynomial S R} {v : S} :
  pderivative v (C a * f) = C a * pderivative v f :=
by rw [pderivative_mul, pderivative_C, zero_mul, zero_add]

end pderivative

end mv_polynomial
