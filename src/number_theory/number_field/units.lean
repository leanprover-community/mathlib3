/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import number_theory.number_field.norm

/-!
# Units of a number field
We prove results about the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K`.

## Main results
* `number_field.is_unit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if
`|norm ℚ x| = 1`

## Tags
number field, units
 -/

open_locale number_field

noncomputable theory

open number_field units

section rat

lemma rat.ring_of_integers.is_unit_iff {x : 𝓞 ℚ} :
  is_unit x ↔ ((x : ℚ) = 1) ∨ ((x : ℚ) = -1) :=
by simp_rw [(is_unit_map_iff (rat.ring_of_integers_equiv : 𝓞 ℚ →+* ℤ) x).symm, int.is_unit_iff,
  ring_equiv.coe_to_ring_hom, ring_equiv.map_eq_one_iff, ring_equiv.map_eq_neg_one_iff,
  ← subtype.coe_injective.eq_iff, add_subgroup_class.coe_neg, algebra_map.coe_one]

end rat

variables (K : Type*) [field K]

section is_unit

local attribute [instance] number_field.ring_of_integers_algebra

variable {K}

lemma is_unit_iff_norm [number_field K] (x : 𝓞 K) :
  is_unit x ↔ |(ring_of_integers.norm ℚ x : ℚ)| = 1 :=
by { convert (ring_of_integers.is_unit_norm ℚ).symm,
  rw [← abs_one, abs_eq_abs, ← rat.ring_of_integers.is_unit_iff], }

end is_unit
