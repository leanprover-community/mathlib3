/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import group_theory.torsion
import number_theory.number_field.embeddings
import number_theory.number_field.norm
import ring_theory.roots_of_unity

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

open finite_dimensional

lemma is_unit_iff_norm [number_field K] (x : 𝓞 K) :
  is_unit x ↔ abs (ring_of_integers.norm ℚ x : ℚ) = 1 :=
begin
  letI : algebra K (algebraic_closure K) := algebraic_closure.algebra K,
  let L := normal_closure ℚ K (algebraic_closure K),
  haveI : finite_dimensional K L := finite_dimensional.right ℚ K L,
  haveI : is_alg_closure ℚ (algebraic_closure K) :=
    is_alg_closure.of_algebraic ℚ K (algebraic_closure K) (number_field.is_algebraic K),
  haveI : is_galois K L := is_galois.tower_top_of_is_galois ℚ K L,
  suffices : is_unit (ring_of_integers.norm K (algebra_map (𝓞 K) (𝓞 L) x)) ↔
    |(ring_of_integers.norm ℚ (algebra_map (𝓞 K) (𝓞 L) x) : ℚ)| = 1,
  { convert this using 1,
    { rw (_ : ring_of_integers.norm K (algebra_map (𝓞 K) (𝓞 L) x) = x ^ (finrank K L)),
      { rw is_unit_pow_iff,
        exact pos_iff_ne_zero.mp finrank_pos, },
      { rw [← subtype.coe_inj, ring_of_integers.coe_norm_algebra_map, algebra.norm_algebra_map,
        subsemiring_class.coe_pow], }},
    { rw [ring_of_integers.norm_apply_coe, ring_of_integers.norm_apply_coe,
        show (algebra_map (𝓞 K) (𝓞 L) x : L) = algebra_map K L (x : K), by refl,
        ←algebra.norm_norm ℚ K (algebra_map K L x : L), algebra.norm_algebra_map, map_pow, abs_pow],
      nth_rewrite 1 ← one_pow (finrank K L),
      rw pow_left_inj (abs_nonneg _ : 0 ≤ |(algebra.norm ℚ) ↑x|) zero_le_one
      (@finrank_pos K L _ _ _ _ _), }},
  { rw [ring_of_integers.is_unit_norm K, ← abs_one, abs_eq_abs, ← rat.ring_of_integers.is_unit_iff],
    exact (ring_of_integers.is_unit_norm ℚ).symm, },
end

end is_unit

namespace number_field.units

open number_field number_field.infinite_place

/-- The `monoid_hom` from the group of units `(𝓞 K)ˣ` to the field `K`. -/
def coe_to_field : (𝓞 K)ˣ →* K := (coe_hom K).comp  (map (algebra_map (𝓞 K) K))

lemma coe_to_field.injective : function.injective (coe_to_field K) :=
λ _ _ h, eq_iff.mp (no_zero_smul_divisors.algebra_map_injective (𝓞 K) K h)

/-- There is a natural coercion from `(𝓞 K)ˣ` to `(𝓞 K)` and then from `(𝓞 K)` to `K` but it is
useful to also have a direct one from `(𝓞 K)ˣ` to `K`. -/
instance ring_of_integers.units.has_coe : has_coe (𝓞 K)ˣ K := ⟨coe_to_field K⟩

@[ext]
lemma ext {x y : (𝓞 K)ˣ} : x = y ↔ (x : K) = (y : K) := (coe_to_field.injective K).eq_iff.symm

@[simp]
lemma coe_pow {x : (𝓞 K)ˣ} {n : ℕ} : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n :=
map_pow (coe_to_field K) _ _

@[simp]
lemma coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

section torsion

/-- The torsion subgroup of the group of units. -/
def torsion : subgroup (𝓞 K)ˣ := comm_group.torsion (𝓞 K)ˣ

lemma mem_torsion (x : (𝓞 K)ˣ) [number_field K] :
  x ∈ torsion K ↔ ∀ w : infinite_place K, w x = 1 :=
begin
  rw [eq_iff_eq (x : K) 1, torsion, comm_group.mem_torsion, is_of_fin_order_iff_pow_eq_one],
  refine ⟨_, λ h, _⟩,
  { rintros ⟨n, h1, h2⟩ φ,
    convert @norm_map_one_of_pow_eq_one _ _ _ _ φ.to_monoid_hom _ ⟨n, h1⟩ _,
    rwa [ext, coe_pow, coe_one] at h2, },
  { obtain ⟨n, hn, hx⟩ := embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    refine ⟨n, hn, by { rw [ext, coe_pow, coe_one]; exact hx, }⟩},
end

lemma torsion_finite [number_field K] : finite (torsion K) :=
begin
  refine set.finite_coe_iff.mpr (set.finite.of_finite_image _
    ((coe_to_field.injective K).inj_on _)),
  refine (embeddings.finite_of_norm_le K ℂ 1).subset (λ a ha, _),
  rcases ha with ⟨⟨u, _, _, _⟩, hu, rfl⟩,
  refine ⟨u.2, (le_iff_le _ 1).mp _⟩,
  convert λ w, le_of_eq (((mem_torsion K _).mp hu) w) using 1,
end

instance [number_field K] : fintype (torsion K) := @fintype.of_finite (torsion K) (torsion_finite K)

lemma torsion_cyclic [number_field K] : is_cyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion group of the units of `K`. -/
def torsion_order [number_field K] : ℕ+ := ⟨fintype.card (torsion K), fintype.card_pos⟩

lemma torsion_eq_roots_of_unity [number_field K]  :
  torsion K = roots_of_unity (torsion_order K) (𝓞 K) :=
begin
  ext1,
  rw [torsion, mem_roots_of_unity],
  refine ⟨λ h, _, λ h, _⟩,
  { exact subtype.ext_iff.mp (@pow_card_eq_one (torsion K) ⟨x, h⟩ _ _), },
  { rw [comm_group.mem_torsion, is_of_fin_order_iff_pow_eq_one],
    exact ⟨torsion_order K, (torsion_order K).pos, h⟩,}
end

end torsion

end number_field.units
