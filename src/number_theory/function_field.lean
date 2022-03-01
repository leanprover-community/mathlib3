/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
import field_theory.ratfunc
import ring_theory.algebraic
import ring_theory.dedekind_domain.integral_closure
import ring_theory.integrally_closed

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions
 - `function_field Fq F` states that `F` is a function field over the (finite) field `Fq`,
   i.e. it is a finite extension of the field of rational functions in one variable over `Fq`.
 - `function_field.ring_of_integers` defines the ring of integers corresponding to a function field
    as the integral closure of `polynomial Fq` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like `finite Fq` or
`is_scalar_tower Fq[X] (fraction_ring Fq[X]) F` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
function field, ring of integers
-/

noncomputable theory
open_locale non_zero_divisors polynomial

variables (Fq F : Type) [field Fq] [field F]

/-- `F` is a function field over the finite field `Fq` if it is a finite
extension of the field of rational functions in one variable over `Fq`.

Note that `F` can be a function field over multiple, non-isomorphic, `Fq`.
-/
abbreviation function_field [algebra (ratfunc Fq) F] : Prop :=
finite_dimensional (ratfunc Fq) F

/-- `F` is a function field over `Fq` iff it is a finite extension of `Fq(t)`. -/
protected lemma function_field_iff (Fqt : Type*) [field Fqt]
  [algebra Fq[X] Fqt] [is_fraction_ring Fq[X] Fqt]
  [algebra (ratfunc Fq) F] [algebra Fqt F]
  [algebra Fq[X] F] [is_scalar_tower Fq[X] Fqt F]
  [is_scalar_tower Fq[X] (ratfunc Fq) F] :
  function_field Fq F ↔ finite_dimensional Fqt F :=
begin
  let e := is_localization.alg_equiv Fq[X]⁰ (ratfunc Fq) Fqt,
  have : ∀ c (x : F), e c • x = c • x,
  { intros c x,
    rw [algebra.smul_def, algebra.smul_def],
    congr,
    refine congr_fun _ c,
    refine is_localization.ext (non_zero_divisors (Fq[X])) _ _ _ _ _ _ _;
      intros; simp only [alg_equiv.map_one, ring_hom.map_one, alg_equiv.map_mul, ring_hom.map_mul,
                         alg_equiv.commutes, ← is_scalar_tower.algebra_map_apply], },
  split; intro h; resetI,
  { let b := finite_dimensional.fin_basis (ratfunc Fq) F,
    exact finite_dimensional.of_fintype_basis (b.map_coeffs e this) },
  { let b := finite_dimensional.fin_basis Fqt F,
    refine finite_dimensional.of_fintype_basis (b.map_coeffs e.symm _),
    intros c x, convert (this (e.symm c) x).symm, simp only [e.apply_symm_apply] },
end

namespace function_field

/-- The function field analogue of `number_field.ring_of_integers`:
`function_field.ring_of_integers Fq Fqt F` is the integral closure of `Fq[t]` in `F`.

We don't actually assume `F` is a function field over `Fq` in the definition,
only when proving its properties.
-/
def ring_of_integers [algebra Fq[X] F] := integral_closure Fq[X] F

namespace ring_of_integers

variables [algebra Fq[X] F]

instance : is_domain (ring_of_integers Fq F) :=
(ring_of_integers Fq F).is_domain

instance : is_integral_closure (ring_of_integers Fq F) Fq[X] F :=
integral_closure.is_integral_closure _ _

variables [algebra (ratfunc Fq) F] [function_field Fq F]
variables [is_scalar_tower Fq[X] (ratfunc Fq) F]

instance : is_fraction_ring (ring_of_integers Fq F) F :=
integral_closure.is_fraction_ring_of_finite_extension (ratfunc Fq) F

instance : is_integrally_closed (ring_of_integers Fq F) :=
integral_closure.is_integrally_closed_of_finite_extension (ratfunc Fq)

instance [is_separable (ratfunc Fq) F] :
  is_dedekind_domain (ring_of_integers Fq F) :=
is_integral_closure.is_dedekind_domain Fq[X] (ratfunc Fq) F _

end ring_of_integers

end function_field
