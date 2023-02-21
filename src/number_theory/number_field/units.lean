/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import group_theory.torsion
import number_theory.number_field.embeddings
import number_theory.number_field.norm
import ring_theory.roots_of_unity

import sandbox

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

namespace number_field.units

/-- The `monoid_hom` from the group of units `(𝓞 K)ˣ` to the field `K`. -/
def coe_to_field : (𝓞 K)ˣ →* K := (coe_hom K).comp  (map (algebra_map (𝓞 K) K))

lemma coe_to_field.injective : function.injective (coe_to_field K) :=
λ _ _ h, eq_iff.mp (no_zero_smul_divisors.algebra_map_injective ↥(𝓞 K) K h)

/-- There is a natural coercion from `(𝓞 K)ˣ` to `(𝓞 K)` and then from `(𝓞 K)` to `K` but it is
useful to also have a direct one from `(𝓞 K)ˣ` to `K`. -/
instance ring_of_integers.units.has_coe : has_coe (𝓞 K)ˣ K := ⟨coe_to_field K⟩

section coe_to_field

variable {K}

@[simp]
lemma coe_to_field.ext {x y : (𝓞 K)ˣ} : (x : K) = (y : K) ↔ x = y :=
(coe_to_field.injective K).eq_iff

@[simp]
lemma coe_to_field.map_inv {x : (𝓞 K)ˣ} : ((x⁻¹ : (𝓞 K)ˣ) : K) = (x : K)⁻¹ :=
map_inv (coe_to_field K) x

@[simp]
lemma coe_to_field.map_pow {x : (𝓞 K)ˣ} {n : ℕ} : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n :=
map_pow (coe_to_field K) x n

@[simp]
lemma coe_to_field.map_zpow {x : (𝓞 K)ˣ} {n : ℤ} : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n :=
map_zpow (coe_to_field K) x n

@[simp]
lemma coe_to_field.map_mul {x y : (𝓞 K)ˣ} : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K) := rfl

@[simp]
lemma coe_to_field.map_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

@[simp]
lemma coe_to_field.ne_zero {x : (𝓞 K)ˣ} : (x : K) ≠ 0 :=
subtype.coe_injective.ne_iff.2 (units.ne_zero x)

end coe_to_field

section is_unit

local attribute [-instance] algebraic_closure.algebra
local attribute [instance] number_field.ring_of_integers_algebra

open finite_dimensional

lemma is_unit_iff_norm.of_is_galois [number_field K] [is_galois ℚ K] (x : 𝓞 K) :
  is_unit x ↔ abs (ring_of_integers.norm ℚ x : ℚ) = 1 := by
rw [← abs_one, abs_eq_abs, ← @ring_of_integers.is_unit_norm _ ℚ, rat.ring_of_integers.is_unit_iff]

example [number_field K] (x : 𝓞 K) : is_unit x ↔ abs (ring_of_integers.norm ℚ x : ℚ) = 1 :=
begin
--  haveI : algebra K (algebraic_closure K) := algebraic_closure.algebra K,
  haveI : char_zero (algebraic_closure K) :=
    char_zero_of_injective_algebra_map (algebra_map K _).injective,
  let L := normal_closure ℚ K (algebraic_closure K),
  haveI : is_alg_closure K (algebraic_closure K) := algebraic_closure.is_alg_closure K,
  haveI : normal ℚ (algebraic_closure K) := normal_algebra_closure_of_is_algebraic ℚ K _ _,
  haveI : finite_dimensional K L := finite_dimensional.right ℚ K _,
  haveI : is_galois K L := {
    to_is_separable := sorry,
    to_normal :=
    begin
      convert normal_closure.normal ℚ K (algebraic_closure K),
      sorry,
    end,

  },
  haveI : is_galois ℚ L := sorry,
  have t1 := @ring_of_integers.is_unit_norm L K _ _ _ _ _ (algebra_map (𝓞 K) (𝓞 L) x),
--  haveI : algebra.is_algebraic ℚ K := sorry,
  have t2 := is_unit_iff_norm.of_is_galois L (algebra_map (𝓞 K) (𝓞 L) x),
  have t3 := t1.trans t2,
  have hs : ring_of_integers.norm K (algebra_map (𝓞 K) (𝓞 L) x) = x ^ (finrank K L),
  { sorry, },
  convert t3 using 1,
  { rw hs,
    rw is_unit_pow_iff,
    rw ← pos_iff_ne_zero,
    exact finite_dimensional.finrank_pos, },
  { simp only [ring_of_integers.norm_apply_coe, eq_iff_iff],
    have t4 := algebra.norm_norm ℚ K L (algebra_map (𝓞 K) (𝓞 L) x),
    rw ← t4,
    rw (_ : (algebra_map (𝓞 K) (𝓞 L) x : L) = algebra_map K L (x : K)),
    { rw algebra.norm_algebra_map,
      have : |(algebra.norm ℚ) ((x : K) ^ finrank K L)| = 1 ↔ |(algebra.norm ℚ) (x : K)| = 1,
      { rw [map_pow, abs_pow],
        nth_rewrite 0 (_ : (1 : ℚ) = 1 ^ finrank K L),
        rw pow_left_inj _ _ _,
        { exact abs_nonneg _, },
        { norm_num, },
        { exact finite_dimensional.finrank_pos, }},
      rw this,
    },
    { refl, }},
end

#exit

example (L : Type*) [field L] [number_field L] [number_field K] (x : 𝓞 K) [algebra K L]
  [finite_dimensional K L] [is_scalar_tower ℚ K L]
  [is_galois ℚ L] : is_unit x ↔ abs (ring_of_integers.norm ℚ x : ℚ) = 1 :=
begin
  haveI : is_galois K L := is_galois.tower_top_of_is_galois ℚ K L,
  letI : algebra (𝓞 K) (𝓞 L) := number_field.ring_of_integers_algebra _ _,
  have t1 := @ring_of_integers.is_unit_norm L K _ _ _ _ _ (algebra_map (𝓞 K) (𝓞 L) x),
  have t2 := is_unit_iff_norm.of_is_galois L (algebra_map (𝓞 K) (𝓞 L) x),
  have t3 := t1.trans t2,
  convert t3 using 1,
  { suffices : ring_of_integers.norm K (algebra_map (𝓞 K) (𝓞 L) x) = x ^ (finrank K L),
    { rw this,
      rw is_unit_pow_iff,
      rw ← pos_iff_ne_zero,
      exact finite_dimensional.finrank_pos, },
    { have : function.injective (algebra_map (𝓞 K) (𝓞 L)) := sorry,
      apply (function.injective.eq_iff this).mp,
      have : function.injective (coe : (𝓞 L) → L) := sorry,
      apply (function.injective.eq_iff this).mp,
      rw ring_of_integers.coe_algebra_map_norm,
      rw (_ : ↑((algebra_map (𝓞 K) (𝓞 L)) x) = (algebra_map K L x)),
      { rw algebra.norm_algebra_map,
        refl, },
      { refl, }}},
  { have t4 := ring_of_integers.norm_composition ℚ K (algebra_map (𝓞 K) (𝓞 L) x),
    rw ← t4,
    suffices : ring_of_integers.norm K (algebra_map (𝓞 K) (𝓞 L) x) = x ^ (finrank K L),
    { rw this,
      simp only [ring_of_integers.norm_apply_coe, map_pow, subsemiring_class.coe_pow, abs_pow,
        eq_iff_iff],
      have : |(algebra.norm ℚ) (x : K)| ^ finrank K L = 1 ↔ |(algebra.norm ℚ) (x : K)| = 1,
      { nth_rewrite 0 (_ : (1 : ℚ) = 1 ^ finrank K L),
        rw pow_left_inj _ _ _,
        { exact abs_nonneg _, },
        { norm_num, },
        { exact finite_dimensional.finrank_pos, }},
      rw this, },
    { sorry, }},
end


end is_unit

#exit

lemma is_unit_iff_norm [number_field K] (x : 𝓞 K) :
  is_unit x ↔ abs (ring_of_integers.norm ℚ x : ℚ) = 1 :=
begin
  set L := normal_closure ℚ K (algebraic_closure K),
  have h1 : normal ℚ (algebraic_closure K) :=
    is_alg_closed.normal.of_algebraic (number_field.is_algebraic K),
  have h2 : finite_dimensional K L := sorry,
  have h3 : normal ℚ L := @normal_closure.normal ℚ K _ _ _ (algebraic_closure K) _ _ _ _ h1,
  have h4 : is_galois K L := sorry,

  have t1 := @ring_of_integers.is_unit_norm L K _ _ _ h2 h4 _, -- (algebra_map (𝓞 K) (𝓞 L) x),
  have t2 := is_unit_iff_norm.of_is_galois L,
--    (algebra_map (𝓞 K) (𝓞 L) x),
--  have t3 := t1.trans t2,
  sorry,
end

#exit

  clear t1,
  clear t2,
  convert t3 using 1,
  { rw toto,
    rw is_unit_pow_iff,
    rw ← pos_iff_ne_zero,
    exact finite_dimensional.finrank_pos, },
  { have := congr_arg (coe : (𝓞 ℚ) → ℚ)
    (ring_of_integers.norm_composition ℚ K (algebra_map (𝓞 K) (𝓞 L) x)),

    rw this,


    have t4 := algebra.norm_composition ℚ K L (algebra_map K L x),

    rw ring_of_integers.coe_norm_algebra_map,

    simp_rw ring_of_integers.norm,
    simp only [monoid_hom.restrict_apply, monoid_hom.cod_restrict_apply],
    have : (algebra_map (𝓞 K) (𝓞 L) x : L) = algebra_map K L (x : K) := rfl,
    simp_rw this,
    rw ← abs_one,
    rw abs_eq_abs,
    rw abs_eq_abs,
    have t4 := algebra.norm_composition ℚ K L (algebra_map K L x),
    simp,
    rw ← t4,
  },
end

#exit

  rw ring_of_integers.toto at t3,
  simp_rw ring_of_integers.norm at t3,
  simp only [monoid_hom.restrict_apply, monoid_hom.cod_restrict_apply] at t3,
  have : (algebra_map (𝓞 K) (𝓞 L) x : L) = algebra_map K L (x : K) := rfl,
  simp_rw this at t3,
  simp at t3,
  convert t3 using 1,

  sorry,
end

#exit

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

#exit

section torsion

open number_field number_field.infinite_place

/-- The torsion subgroup of the group of units. -/
def torsion : subgroup (𝓞 K)ˣ := comm_group.torsion (𝓞 K)ˣ

lemma mem_torsion (x : (𝓞 K)ˣ) [number_field K] :
  x ∈ torsion K ↔ ∀ w : infinite_place K, w x = 1 :=
begin
  rw (eq_iff_eq x 1 : (∀ w : infinite_place K, w x = 1) ↔ ∀ (φ : K →+* ℂ), ‖φ (x : K)‖ = 1),
  rw [torsion, comm_group.mem_torsion, is_of_fin_order_iff_pow_eq_one],
  split,
  { rintros ⟨n, ⟨hn1, hn2⟩⟩ φ,
    lift n to ℕ+ using hn1,
    rw [← units_to_field.ext, units_to_field.map_pow] at hn2,
    exact norm_map_one_of_pow_eq_one φ.to_monoid_hom hn2, },
  { intro h,
    obtain ⟨n , ⟨hn, hx⟩⟩ := embeddings.pow_eq_one_of_norm_eq_one K ℂ x.1.2 h,
    exact ⟨n, ⟨hn, by { rwa [← units_to_field.ext, units_to_field.map_pow], }⟩⟩, },
end

lemma torsion_finite [number_field K] : finite (torsion K) :=
begin
  suffices : ((coe : (𝓞 K)ˣ → K) '' { x : (𝓞 K)ˣ | x ∈ (torsion K )}).finite,
  { exact set.finite_coe_iff.mpr (set.finite.of_finite_image this
      ((units_to_field.injective K).inj_on _)), },
  refine (embeddings.finite_of_norm_le K ℂ 1).subset _,
  rintros a ⟨⟨u, _, _, _⟩, ⟨hu, rfl⟩⟩,
  split,
  { exact u.2, },
  { rw ← le_iff_le,
    convert λ w, le_of_eq (((mem_torsion K _).mp hu) w) using 1, },
end

instance [number_field K] : fintype (torsion K) :=
@fintype.of_finite (torsion K) (torsion_finite K)

lemma torsion_cyclic [number_field K] : is_cyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion group of the units of `K`. -/
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
    have := congr_arg (coe : (𝓞 K)ˣ → (𝓞 K)) this,
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
