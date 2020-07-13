/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark.
-/
import data.polynomial
open polynomial finset

/-!
# Polynomials

Eventually, much of data/polynomial.lean should land here.

## Main results

We relate `eval` and the constant coefficient map to `aeval`, so we can use `alg_hom` properties.

We define a `monoid_hom` of type `polynomial R →* R`,
- `leading_coeff_monoid_hom`
-/

universes u w

noncomputable theory

variables {R : Type u} {α : Type w}

namespace polynomial

section comm_semiring
variables [comm_semiring R]

lemma coe_aeval_eq_eval (r : R) : (aeval R R r: polynomial R → R) = eval r := rfl

lemma coeff_zero_eq_aeval_zero (p : polynomial R) : p.coeff 0 = aeval R R 0 p :=
by { rw coeff_zero_eq_eval_zero, rw coe_aeval_eq_eval, }

end comm_semiring

section integral_domain
variable [integral_domain R]

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` is an `integral_domain`, and thus
  `leading_coeff` is multiplicative -/
def leading_coeff_monoid_hom : polynomial R →* R :=
{ to_fun := leading_coeff,
  map_one' := by simp,
  map_mul' := leading_coeff_mul }

@[simp] lemma leading_coeff_monoid_hom_apply (p : polynomial R) :
  leading_coeff_monoid_hom p = leading_coeff p := rfl

end integral_domain
end polynomial
