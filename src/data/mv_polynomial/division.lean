/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra.division
import data.mv_polynomial.basic

/-!
# Division of `mv_polynomial` by monomials

## Main definitions

* `mv_polynomial.div_monomial s x`: divides `x` by the monomial `mv_polynomial.of k G s`
* `mv_polynomial.mod_monomial s x`: the remainder upon dividing `x` by the monomial
  `mv_polynomial.of k G s`.

## Main results

* `mv_polynomial.div_monomial_add_mod_monomial`, `mv_polynomial.mod_monomial_add_div_monomial`:
  `div_monomial` and `mod_monomial` are well-behaved as quotient and remainder operators.

## Implementation notes

Most of the results in this file should be first proved in the generality of `add_monoid_algebra`,
and then specialized to `mv_polynomial` for convenience.

-/


variables {σ R : Type*} [comm_semiring R]

namespace mv_polynomial

section

/-- Divide by `monomial 1 s`, discarding terms not divisible by this. -/
noncomputable def div_monomial (s : σ →₀ ℕ) : mv_polynomial σ R →+ mv_polynomial σ R :=
add_monoid_algebra.div_of s

@[simp] lemma coeff_div_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R) (s' : σ →₀ ℕ) :
  coeff s' (div_monomial s x) = coeff (s + s') x := rfl

@[simp] lemma support_div_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R)  :
  (div_monomial s x).support = x.support.preimage _ ((add_right_injective s).inj_on _) := rfl

lemma div_monomial_zero (x : mv_polynomial σ R) : div_monomial 0 x = x :=
add_monoid_algebra.div_of_zero x

lemma div_monomial_add (a b : σ →₀ ℕ) (x : mv_polynomial σ R)  :
  div_monomial (a + b) x = div_monomial b (div_monomial a x) :=
x.div_of_add _ _

/-- The remainder upon division by `monomial 1 s`. -/
noncomputable def mod_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R) : mv_polynomial σ R :=
x.mod_of s

@[simp] lemma coeff_mod_monomial_of_not_le {s' s : σ →₀ ℕ} (x : mv_polynomial σ R) (h : ¬s ≤ s') :
  coeff s' (mod_monomial s x) = coeff s' x :=
x.mod_of_apply_of_not_le h

@[simp] lemma coeff_mod_monomial_of_le {s' s : σ →₀ ℕ} (x : mv_polynomial σ R) (h : s ≤ s') :
  coeff s' (mod_monomial s x) = 0 :=
x.mod_of_apply_of_le h

lemma div_of_add_mod_of (x : mv_polynomial σ R) (s : σ →₀ ℕ) :
  monomial s 1 * div_monomial s x + mod_monomial s x = x :=
x.div_of_add_mod_of _ _

lemma mod_of_add_div_of (x : mv_polynomial σ R) (s : σ →₀ ℕ) :
  mod_monomial s x + monomial s 1 * div_monomial s x = x :=
x.mod_of_add_div_of _ _

end

end mv_polynomial
