/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/

import algebra.field
import data.rat.basic
import ring_theory.algebraic
import ring_theory.dedekind_domain
import ring_theory.integral_closure
import ring_theory.polynomial.rational_root

/-!
# Number fields
This file defines a number field and the ring of integers corresponding to it.

## Main definitions
 - `number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
number field, ring of integers
-/

/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
class number_field (K : Type*) [field K] : Prop :=
[to_char_zero : char_zero K]
[to_finite_dimensional : finite_dimensional ℚ K]

open function
open_locale classical big_operators

namespace number_field
variables (K : Type*) [field K] [number_field K]

-- See note [lower instance priority]
attribute [priority 100, instance] number_field.to_char_zero number_field.to_finite_dimensional

protected lemma is_algebraic : algebra.is_algebraic ℚ K := algebra.is_algebraic_of_finite

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
@[nolint unused_arguments] -- There are multiple definitions of rings of integers.
def ring_of_integers := integral_closure ℤ K

namespace ring_of_integers

variables {K}

lemma is_integral_coe (x : ring_of_integers K) : is_integral ℤ (x : K) :=
x.2

variables (K)

lemma char_zero.of_algebra {R : Type*} (S : Type*) [comm_semiring R] [semiring S] [algebra R S]
  [char_zero S] : char_zero R :=
⟨begin
  suffices : injective (algebra_map R S ∘ coe),
  { exact injective.of_comp this },
  convert char_zero.cast_injective,
  ext n,
  rw [function.comp_app, ← (algebra_map ℕ _).eq_nat_cast, ← ring_hom.comp_apply,
      ring_hom.eq_nat_cast],
  all_goals { apply_instance }
end⟩

instance : char_zero (ring_of_integers K) := char_zero.of_algebra K

-- TODO: show `ring_of_integers K` is a Dedekind domain

end ring_of_integers

end number_field

namespace rat

open number_field

instance rat.finite_dimensional : finite_dimensional ℚ ℚ :=
(infer_instance : is_noetherian ℚ ℚ)

instance rat.number_field : number_field ℚ :=
{ to_char_zero := infer_instance,
  to_finite_dimensional := by { convert rat.finite_dimensional,
             -- The vector space structure of `ℚ` over itself can arise in multiple ways:
             -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
             -- all fields have a canonical embedding of `ℚ` (used in `number_field`).
             -- Show that these coincide:
             ext, simp [algebra.smul_def] } }

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ring_of_integers_equiv : ring_of_integers ℚ ≃+* ℤ :=
ring_equiv.symm $
ring_equiv.of_bijective (algebra_map ℤ (ring_of_integers ℚ))
  ⟨λ x y hxy, int.cast_injective $
      show (x : ring_of_integers ℚ) = (y : ring_of_integers ℚ), by simpa using hxy,
   λ y, begin
     obtain ⟨x, hx⟩ := unique_factorization_monoid.integer_of_integral
       (ring_of_integers.is_integral_coe y),
     use x,
     refine subtype.coe_injective _,
     rw [← hx, subalgebra.coe_algebra_map]
   end⟩

end rat
