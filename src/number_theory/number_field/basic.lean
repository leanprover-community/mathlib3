/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/

import algebra.char_p.algebra
import ring_theory.dedekind_domain.integral_closure

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

open function module
open_locale classical big_operators non_zero_divisors

/-- `ℤ` with its usual ring structure is not a field. -/
lemma int.not_is_field : ¬ is_field ℤ :=
λ h, int.not_even_one $ (h.mul_inv_cancel two_ne_zero).imp $ λ a, (by rw ← two_mul; exact eq.symm)

namespace number_field

variables (K L : Type*) [field K] [field L] [nf : number_field K]

include nf

-- See note [lower instance priority]
attribute [priority 100, instance] number_field.to_char_zero number_field.to_finite_dimensional

protected lemma is_algebraic : algebra.is_algebraic ℚ K := algebra.is_algebraic_of_finite _ _

omit nf

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ring_of_integers := integral_closure ℤ K

localized "notation (name := ring_of_integers)
  `𝓞` := number_field.ring_of_integers" in number_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 K ↔ is_integral ℤ x := iff.rfl

lemma is_integral_of_mem_ring_of_integers {K : Type*} [field K] {x : K} (hx : x ∈ 𝓞 K) :
  is_integral ℤ (⟨x, hx⟩ : 𝓞 K) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP]
end

/-- Given an algebra between two fields, create an algebra between their two rings of integers.

For now, this is not an instance by default as it creates an equal-but-not-defeq diamond with
`algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on subtypes. This
will likely change in Lean 4. -/
def ring_of_integers_algebra [algebra K L] : algebra (𝓞 K) (𝓞 L) := ring_hom.to_algebra
{ to_fun := λ k, ⟨algebra_map K L k, is_integral.algebra_map k.2⟩,
  map_zero' := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_zero, map_zero],
  map_one'  := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_one, map_one],
  map_add' := λ x y, subtype.ext $ by simp only [map_add, subalgebra.coe_add, subtype.coe_mk],
  map_mul' := λ x y, subtype.ext $ by simp only [subalgebra.coe_mul, map_mul, subtype.coe_mk] }

namespace ring_of_integers

variables {K}

instance [number_field K] : is_fraction_ring (𝓞 K) K :=
integral_closure.is_fraction_ring_of_finite_extension ℚ _

instance : is_integral_closure (𝓞 K) ℤ K :=
integral_closure.is_integral_closure _ _

instance [number_field K] : is_integrally_closed (𝓞 K) :=
integral_closure.is_integrally_closed_of_finite_extension ℚ

lemma is_integral_coe (x : 𝓞 K) : is_integral ℤ (x : K) :=
x.2

lemma map_mem {F L : Type*} [field L] [char_zero K] [char_zero L]
  [alg_hom_class F ℚ K L] (f : F) (x : 𝓞 K) : f x ∈ 𝓞 L :=
(mem_ring_of_integers _ _).2 $ map_is_integral_int f $ ring_of_integers.is_integral_coe x

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def equiv (R : Type*) [comm_ring R] [algebra R K]
  [is_integral_closure R ℤ K] : 𝓞 K ≃+* R :=
(is_integral_closure.equiv ℤ R K _).symm.to_ring_equiv

variable (K)
include nf

instance : char_zero (𝓞 K) := char_zero.of_module _ K

instance : is_noetherian ℤ (𝓞 K) := is_integral_closure.is_noetherian _ ℚ K _

/-- The ring of integers of a number field is not a field. -/
lemma not_is_field : ¬ is_field (𝓞 K) :=
begin
  have h_inj : function.injective ⇑(algebra_map ℤ (𝓞 K)),
  { exact ring_hom.injective_int (algebra_map ℤ (𝓞 K)) },
  intro hf,
  exact int.not_is_field
    (((is_integral_closure.is_integral_algebra ℤ K).is_field_iff_is_field h_inj).mpr hf)
end

instance : is_dedekind_domain (𝓞 K) :=
is_integral_closure.is_dedekind_domain ℤ ℚ K _

instance : free ℤ (𝓞 K) := is_integral_closure.module_free ℤ ℚ K (𝓞 K)

instance : is_localization (algebra.algebra_map_submonoid (𝓞 K) ℤ⁰) K :=
is_integral_closure.is_localization ℤ ℚ K (𝓞 K)

/-- A ℤ-basis of the ring of integers of `K`. -/
noncomputable def basis : basis (free.choose_basis_index ℤ (𝓞 K)) ℤ (𝓞 K) :=
free.choose_basis ℤ (𝓞 K)

end ring_of_integers

include nf

/-- A basis of `K` over `ℚ` that is also a basis of `𝓞 K` over `ℤ`. -/
noncomputable def integral_basis : basis (free.choose_basis_index ℤ (𝓞 K)) ℚ K :=
basis.localization_localization ℚ (non_zero_divisors ℤ) K (ring_of_integers.basis K)

@[simp]
lemma integral_basis_apply (i : free.choose_basis_index ℤ (𝓞 K)) :
  integral_basis K i = algebra_map (𝓞 K) K (ring_of_integers.basis K i) :=
basis.localization_localization_apply ℚ (non_zero_divisors ℤ) K (ring_of_integers.basis K) i

lemma ring_of_integers.rank  :
  finite_dimensional.finrank ℤ (𝓞 K) = finite_dimensional.finrank ℚ K :=
is_integral_closure.rank ℤ ℚ K (𝓞 K)

end number_field

namespace rat

open number_field

instance number_field : number_field ℚ :=
{ to_char_zero := infer_instance,
  to_finite_dimensional :=
    -- The vector space structure of `ℚ` over itself can arise in multiple ways:
    -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
    -- all char 0 fields have a canonical embedding of `ℚ` (used in `number_field`).
    -- Show that these coincide:
    by convert (infer_instance : finite_dimensional ℚ ℚ), }

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ring_of_integers_equiv : ring_of_integers ℚ ≃+* ℤ :=
ring_of_integers.equiv ℤ

end rat

namespace adjoin_root

section

open_locale polynomial

local attribute [-instance] algebra_rat

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : ℚ[X]} [hf : fact (irreducible f)] : number_field (adjoin_root f) :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map ℚ _).injective,
  to_finite_dimensional := by convert (adjoin_root.power_basis hf.out.ne_zero).finite_dimensional }
end

end adjoin_root
