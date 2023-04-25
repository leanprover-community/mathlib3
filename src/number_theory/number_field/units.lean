/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import number_theory.number_field.norm

/-!
 # Units of a number field
This file defines and proves results about the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K`
of a number field `K`.

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
local attribute [-instance] algebraic_closure.algebra

open finite_dimensional

lemma is_unit_iff_norm.of_is_galois [number_field K] [is_galois ℚ K] (x : 𝓞 K) :
  is_unit x ↔ abs (ring_of_integers.norm ℚ x : ℚ) = 1 := by
rw [← abs_one, abs_eq_abs, ← @ring_of_integers.is_unit_norm _ ℚ, rat.ring_of_integers.is_unit_iff]

lemma is_unit_iff_norm [number_field K] (x : 𝓞 K) :
  is_unit x ↔ abs (ring_of_integers.norm ℚ x : ℚ) = 1 :=
begin
  letI : algebra K (algebraic_closure K) := algebraic_closure.algebra K,
  haveI : char_zero (algebraic_closure K) := algebraic_closure.char_zero K,
  let L := normal_closure ℚ K (algebraic_closure K),
  haveI : finite_dimensional K L := finite_dimensional.right ℚ K L,
  haveI : is_alg_closure ℚ (algebraic_closure K) :=
    is_alg_closure.of_algebraic ℚ K (algebraic_closure K) (number_field.is_algebraic K),
  haveI : is_galois K L := is_galois.tower_top_of_is_galois ℚ K L,
  convert (ring_of_integers.is_unit_norm K).trans
    (is_unit_iff_norm.of_is_galois L (algebra_map (𝓞 K) (𝓞 L) x)) using 1,
  { rw (_ : ring_of_integers.norm K (algebra_map (𝓞 K) (𝓞 L) x) = x ^ (finrank K L)),
    { rw is_unit_pow_iff,
      exact pos_iff_ne_zero.mp finrank_pos, },
    apply subtype.coe_injective,
    rw [ring_of_integers.coe_norm_algebra_map, algebra.norm_algebra_map,
      subsemiring_class.coe_pow], },
  { rw [ring_of_integers.norm_apply_coe, ring_of_integers.norm_apply_coe,
      show (algebra_map (𝓞 K) (𝓞 L) x : L) = algebra_map K L (x : K), by refl,
      ← algebra.norm_norm ℚ K (algebra_map K L x : L), algebra.norm_algebra_map, map_pow, abs_pow],
    nth_rewrite 1 ← one_pow (finrank K L),
    rw pow_left_inj (abs_nonneg _ : 0 ≤ |(algebra.norm ℚ) ↑x|) zero_le_one
      (@finrank_pos K L _ _ _ _ _), },
end

end is_unit
