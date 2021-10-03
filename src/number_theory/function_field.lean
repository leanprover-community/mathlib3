/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
import ring_theory.algebraic
import ring_theory.localization
import ring_theory.integrally_closed

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions
 - `function_field Fq F` states that `F` is a function field over the (finite) field `Fq`,
   i.e. it is a finite extension of the field of rational polynomials in one variable over `Fq`.
 - `function_field.ring_of_integers` defines the ring of integers corresponding to a function field
    as the integral closure of `polynomial Fq` in the function field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like `finite Fq` or
`is_scalar_tower (polynomial Fq) (fraction_ring (polynomial Fq)) F` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
function field, ring of integers
-/

noncomputable theory

variables (Fq F : Type) [field Fq] [field F]

/-- `F` is a function field over the finite field `Fq` if it is a finite
extension of the field of rational polynomials in one variable over `Fq`.

Note that `F` can be a function field over multiple, non-isomorphic, `Fq`.
-/
abbreviation function_field [algebra (fraction_ring (polynomial Fq)) F] : Prop :=
finite_dimensional (fraction_ring (polynomial Fq)) F

/-- `F` is a function field over `Fq` iff it is a finite extension of `Fq(t)`. -/
protected lemma function_field_iff (Fqt : Type*) [field Fqt]
  [algebra (polynomial Fq) Fqt] [is_fraction_ring (polynomial Fq) Fqt]
  [algebra (fraction_ring (polynomial Fq)) F] [algebra Fqt F]
  [algebra (polynomial Fq) F] [is_scalar_tower (polynomial Fq) Fqt F]
  [is_scalar_tower (polynomial Fq) (fraction_ring (polynomial Fq)) F] :
  function_field Fq F ↔ finite_dimensional Fqt F :=
begin
  let e := fraction_ring.alg_equiv (polynomial Fq) Fqt,
  have : ∀ c (x : F), e c • x = c • x,
  { intros c x,
    rw [algebra.smul_def, algebra.smul_def],
    congr,
    refine congr_fun _ c,
    refine is_localization.ext (non_zero_divisors (polynomial Fq)) _ _ _ _ _ _ _;
      intros; simp only [alg_equiv.map_one, ring_hom.map_one, alg_equiv.map_mul, ring_hom.map_mul,
                         alg_equiv.commutes, ← is_scalar_tower.algebra_map_apply], },
  split; intro h; resetI,
  { let b := finite_dimensional.fin_basis (fraction_ring (polynomial Fq)) F,
    exact finite_dimensional.of_fintype_basis (b.map_coeffs e this) },
  { let b := finite_dimensional.fin_basis Fqt F,
    refine finite_dimensional.of_fintype_basis (b.map_coeffs e.symm _),
    intros c x, convert (this (e.symm c) x).symm; simp },
end

namespace function_field

/-- The function field analogue of `number_field.ring_of_integers`:
`function_field.ring_of_integers Fq Fqt F` is the integral closure of `Fq[t]` in `F`.

We don't actually assume `F` is a function field over `Fq` in the definition,
only when proving its properties.
-/
def ring_of_integers [algebra (polynomial Fq) F] := integral_closure (polynomial Fq) F

namespace ring_of_integers

variables [algebra (polynomial Fq) F]

instance : integral_domain (ring_of_integers Fq F) :=
(ring_of_integers Fq F).integral_domain

instance : is_integral_closure (ring_of_integers Fq F) (polynomial Fq) F :=
integral_closure.is_integral_closure _ _

variables [algebra (fraction_ring (polynomial Fq)) F] [function_field Fq F]
variables [is_scalar_tower (polynomial Fq) (fraction_ring (polynomial Fq)) F]

instance : is_fraction_ring (ring_of_integers Fq F) F :=
integral_closure.is_fraction_ring_of_finite_extension (fraction_ring (polynomial Fq)) F

instance : is_integrally_closed (ring_of_integers Fq F) :=
integral_closure.is_integrally_closed_of_finite_extension (fraction_ring (polynomial Fq))

-- TODO: show `ring_of_integers Fq F` is a Dedekind domain

end ring_of_integers

end function_field
