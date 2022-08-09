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

* `mv_polynomial.div_monomial s x`: divides `x` by the monomial `mv_polynomial.monomial 1 s`
* `mv_polynomial.mod_monomial s x`: the remainder upon dividing `x` by the monomial
  `mv_polynomial.monomial 1 s`.

## Main results

* `mv_polynomial.div_monomial_add_mod_monomial`, `mv_polynomial.mod_monomial_add_div_monomial`:
  `div_monomial` and `mod_monomial` are well-behaved as quotient and remainder operators.

## Implementation notes

Most of the results in this file should be first proved in the generality of `add_monoid_algebra`,
and then specialized to `mv_polynomial` for convenience.

-/


variables {σ R : Type*} [comm_semiring R]

namespace mv_polynomial

section copied_declarations

/-- Divide by `monomial 1 s`, discarding terms not divisible by this. -/
noncomputable def div_monomial (s : σ →₀ ℕ) : mv_polynomial σ R →+ mv_polynomial σ R :=
add_monoid_algebra.div_of s

@[simp] lemma coeff_div_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R) (s' : σ →₀ ℕ) :
  coeff s' (div_monomial s x) = coeff (s + s') x := rfl

@[simp] lemma support_div_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R)  :
  (div_monomial s x).support = x.support.preimage _ ((add_right_injective s).inj_on _) := rfl

lemma div_monomial_zero (x : mv_polynomial σ R) : div_monomial 0 x = x :=
x.div_of_zero

lemma div_monomial_add (a b : σ →₀ ℕ) (x : mv_polynomial σ R)  :
  div_monomial (a + b) x = div_monomial b (div_monomial a x) :=
x.div_of_add _ _

@[simp] lemma div_monomial_monomial_mul (a : σ →₀ ℕ) (x : mv_polynomial σ R) :
  div_monomial a (monomial a 1 * x) = x :=
x.div_of_of'_mul _

@[simp] lemma div_monomial_mul_monomial (a : σ →₀ ℕ) (x : mv_polynomial σ R) :
  div_monomial a (x * monomial a 1) = x :=
x.div_of_mul_of' _

@[simp] lemma div_monomial_monomial (a : σ →₀ ℕ) :
  div_monomial a (monomial a 1) = (1 : mv_polynomial σ R) :=
add_monoid_algebra.div_of_of' _

/-- The remainder upon division by `monomial 1 s`. -/
noncomputable def mod_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R) : mv_polynomial σ R :=
x.mod_of s

@[simp] lemma coeff_mod_monomial_of_not_le {s' s : σ →₀ ℕ} (x : mv_polynomial σ R) (h : ¬s ≤ s') :
  coeff s' (mod_monomial s x) = coeff s' x :=
x.mod_of_apply_of_not_le h

@[simp] lemma coeff_mod_monomial_of_le {s' s : σ →₀ ℕ} (x : mv_polynomial σ R) (h : s ≤ s') :
  coeff s' (mod_monomial s x) = 0 :=
x.mod_of_apply_of_le h

@[simp] lemma mod_monomial_monomial_mul (s : σ →₀ ℕ) (x : mv_polynomial σ R) :
  mod_monomial s (monomial s 1 * x) = 0 :=
x.mod_of_of'_mul _

@[simp] lemma mod_monomial_mul_monomial (s : σ →₀ ℕ) (x : mv_polynomial σ R):
  mod_monomial s (x * monomial s 1) = 0 :=
x.mod_of_mul_of' _

@[simp] lemma mod_monomial_monomial (s : σ →₀ ℕ) : mod_monomial s (monomial s 1) = 0 :=
add_monoid_algebra.mod_of_of' _

lemma div_monomial_add_mod_monomial (x : mv_polynomial σ R) (s : σ →₀ ℕ) :
  monomial s 1 * div_monomial s x + mod_monomial s x = x :=
x.div_of_add_mod_of _

lemma mod_monomial_add_div_monomial (x : mv_polynomial σ R) (s : σ →₀ ℕ) :
  mod_monomial s x + monomial s 1 * div_monomial s x = x :=
x.mod_of_add_div_of _

end copied_declarations

section X_lemmas

@[simp] lemma div_monomial_X_mul (i : σ) (x : mv_polynomial σ R) :
  div_monomial (finsupp.single i 1) (X i * x) = x :=
div_monomial_monomial_mul _ _

@[simp] lemma div_monomial_X (i : σ) :
  div_monomial (finsupp.single i 1) (X i : mv_polynomial σ R) = 1 :=
(div_monomial_monomial (finsupp.single i 1))

@[simp] lemma div_monomial_mul_X (i : σ) (x : mv_polynomial σ R) :
  div_monomial (finsupp.single i 1) (x * X i) = x :=
div_monomial_mul_monomial _ _

@[simp] lemma mod_monomial_X_mul (i : σ) (x : mv_polynomial σ R) :
  mod_monomial (finsupp.single i 1) (X i * x) = 0 :=
x.mod_of_of'_mul _

@[simp] lemma mod_monomial_mul_X (i : σ) (x : mv_polynomial σ R):
  mod_monomial (finsupp.single i 1) (x * X i) = 0 :=
x.mod_of_mul_of' _

@[simp] lemma mod_monomial_X (i : σ) :
  mod_monomial (finsupp.single i 1) (X i : mv_polynomial σ R) = 0 :=
add_monoid_algebra.mod_of_of' _

lemma div_monomial_add_mod_monomial_single (x : mv_polynomial σ R) (i : σ) :
  X i * div_monomial (finsupp.single i 1) x + mod_monomial (finsupp.single i 1) x = x :=
x.div_of_add_mod_of _

lemma mod_monomial_add_div_monomial_single (x : mv_polynomial σ R) (i : σ) :
  mod_monomial (finsupp.single i 1) x + X i * div_monomial (finsupp.single i 1) x = x :=
x.mod_of_add_div_of _

end X_lemmas

end mv_polynomial
