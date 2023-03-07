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
This file defines and proves results about the group `𝓤 K` of units of the ring of integers `𝓞 K`
of a number field `K`.

 ## Tags
number field, units
 -/

open_locale classical number_field

noncomputable theory

variables (K : Type*) [field K]

localized "notation `𝓤`K := (number_field.ring_of_integers K)ˣ" in number_field.units

namespace number_field.units

open number_field units

/-- The `monoid_hom` from the group of units to the field. -/
def to_field : (𝓤 K) →* K := monoid_hom.comp (coe_hom K) (map (algebra_map (𝓞 K) K))

lemma to_field_injective : function.injective (to_field K) :=
begin
  have t1 : function.injective (coe_hom K) := by ext,
  have t2 : function.injective (units.map (algebra_map (𝓞 K) K).to_monoid_hom) :=
  begin
    intros x y hxy,
    rw units.ext_iff,
    have t1 := congr_arg (coe : Kˣ → K) hxy,
    simp_rw [units.coe_map] at t1,
    exact (no_zero_smul_divisors.algebra_map_injective (𝓞 K) K) t1,
  end,
  rw [to_field, monoid_hom.coe_comp],
  exact function.injective.comp t1 t2,
end

instance ring_of_integers.units.has_coe : has_coe (𝓤 K) K := ⟨to_field K⟩

section coe

variable {K}

@[simp]
lemma coe_ext {x y : 𝓤 K} : (x : K) = (y : K) ↔ x = y := (to_field_injective K).eq_iff

@[simp]
lemma coe_inv {x : 𝓤 K} : ((x⁻¹ : 𝓤 K) : K) = (x : K)⁻¹ := map_inv (to_field K) x

@[simp]
lemma coe_pow {x : 𝓤 K} {n : ℕ} : ((x ^ n : 𝓤 K) : K) = (x : K) ^ n :=
  map_pow (to_field K) x n

@[simp]
lemma coe_zpow {x : 𝓤 K} {n : ℤ} : ((x ^ n : 𝓤 K) : K) = (x : K) ^ n :=
  map_zpow (to_field K) x n

@[simp]
lemma coe_mul {x y : 𝓤 K} : ((x * y : 𝓤 K) : K) = (x : K) * (y : K) := rfl

@[simp]
lemma coe_coe {x : 𝓤 K} : ((x : 𝓞 K) : K) = (x : K) := rfl

@[simp]
lemma coe_one : ((1 : 𝓤 K) : K) = (1 : K) := rfl

@[simp]
lemma coe_ne_zero {x : 𝓤 K} : (x : K) ≠ 0 :=
subtype.coe_injective.ne_iff.2 (units.ne_zero x)

end coe

-- TODO. That should be tautological
lemma is_unit_iff (x : 𝓞 K) (hx : x ≠ 0):
  is_unit x ↔ is_integral ℤ (x⁻¹ : K) :=
begin
  split,
  { rintros ⟨u, rfl⟩,
    convert ring_of_integers.is_integral_coe u.inv,
    simp only [coe_coe, inv_eq_coe_inv, coe_inv], },
  { intro h,
    rw is_unit_iff_exists_inv,
    use ⟨x⁻¹, h⟩,
    apply @subtype.coe_injective K (λ x, x ∈ 𝓞 K),
    simp only [mul_mem_class.coe_mul, subtype.coe_mk, algebra_map.coe_one],
    refine mul_inv_cancel _,
    exact (@subtype.coe_injective K (λ x, x ∈ 𝓞 K)).ne hx, },
end

-- TODO. Make that an iff and simplify the proof
lemma unit.abs_norm [number_field K] (u : 𝓤 K) :
  abs (ring_of_integers.norm ℚ (u : 𝓞 K) : ℚ) = 1 :=
begin
  have t1 := congr_arg (λ x, (ring_of_integers.norm ℚ) x) u.val_inv,
  have t2 := congr_arg rat.ring_of_integers_equiv t1,
  have t3 := congr_arg abs t2,
  simp_rw [map_mul, abs_mul, map_one, abs_one] at t3,
  have t4 := dvd.intro _ t3,
  have t5 :=  int.eq_one_of_dvd_one (abs_nonneg _) t4,
  rw ← abs_one at t5 ⊢,
  rw abs_eq_abs at t5 ⊢,
  cases t5,
  { left,
    have := congr_arg rat.ring_of_integers_equiv.symm t5,
    rw ring_equiv.symm_apply_apply _ _ at this,
    rw map_one at this,
    exact congr_arg (coe : (𝓞 ℚ) → ℚ) this, },
  { right,
    have := congr_arg rat.ring_of_integers_equiv.symm t5,
    rw ring_equiv.symm_apply_apply _ _ at this,
    rw ring_equiv.map_neg_one at this,
    exact congr_arg (coe : (𝓞 ℚ) → ℚ) this, }
end

section torsion

open number_field number_field.infinite_place

/-- The torsion subgroup of the group of units. -/
def torsion : subgroup 𝓤 K := comm_group.torsion (𝓤 K)

lemma mem_torsion (x : (𝓤 K)) [number_field K] :
  x ∈ torsion K ↔ ∀ w : infinite_place K, w x = 1 :=
begin
  rw (eq_iff_eq x 1 : (∀ w : infinite_place K, w x = 1) ↔ ∀ (φ : K →+* ℂ), ‖φ (x : K)‖ = 1),
  rw [torsion, comm_group.mem_torsion, is_of_fin_order_iff_pow_eq_one],
  split,
  { rintros ⟨n, ⟨hn1, hn2⟩⟩ φ,
    lift n to ℕ+ using hn1,
    rw [ ← coe_ext, coe_pow] at hn2,
    exact norm_map_one_of_pow_eq_one φ.to_monoid_hom hn2, },
  { intro h,
    obtain ⟨n , ⟨hn, hx⟩⟩ := embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    exact ⟨n, ⟨hn, by { rwa [← coe_ext, coe_pow], }⟩⟩, },
end

lemma torsion_finite [number_field K] : finite (torsion K) :=
begin
  suffices : ((coe : (𝓤 K) → K) '' { x : (𝓤 K) | x ∈ (torsion K )}).finite,
  { exact set.finite_coe_iff.mpr (set.finite.of_finite_image this
      ((to_field_injective K).inj_on _)), },
  refine (embeddings.finite_of_norm_le K ℂ 1).subset _,
  rintros a ⟨⟨u, _, _, _⟩, ⟨hu, rfl⟩⟩,
  split,
  { exact u.2, },
  { rw ← le_iff_le,
    convert λ w, le_of_eq (((mem_torsion K _).mp hu) w) using 1, },
end

instance [number_field K] : fintype (torsion K) :=
@fintype.of_finite (torsion K) (torsion_finite K)

instance torsion_cyclic [number_field K] : is_cyclic (torsion K) :=
subgroup_units_cyclic _

def torsion_order [number_field K] : ℕ+ :=
begin
  haveI : fintype (torsion K) := fintype.of_finite (torsion K),
  refine ⟨fintype.card (torsion K), _⟩,
  exact fintype.card_pos,
end

lemma torsion_eq_roots_of_unity [number_field K]  :
  torsion K = roots_of_unity (torsion_order K) (𝓞 K) :=
begin
  ext,
  rw mem_roots_of_unity',
  rw torsion_order,
  split,
  { intro hx,
    have := @pow_card_eq_one (torsion K) ⟨x, hx⟩ _ _,
    simp only [submonoid_class.mk_pow, subgroup.mk_eq_one_iff] at this,
    have := congr_arg (coe : (𝓤 K) → (𝓞 K)) this,
    rw units.coe_pow at this,
    convert this, },
  { intro hx,
    rw torsion,
    rw comm_group.mem_torsion,
    rw is_of_fin_order_iff_pow_eq_one,
    use fintype.card (torsion K),
    split,
    { exact fintype.card_pos, },
    { rw units.ext_iff,
      rw units.coe_pow,
      convert hx, }},
end

end torsion

end number_field.units
