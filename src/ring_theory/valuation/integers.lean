/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import ring_theory.valuation.basic

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/

universes u v w

namespace valuation

section ring

variables {R : Type u} {Γ₀ : Type v} [ring R] [linear_ordered_comm_group_with_zero Γ₀]
variables (v : valuation R Γ₀)

/-- The ring of integers under a given valuation is the subring of elements with valuation ≤ 1. -/
def integer : subring R :=
{ carrier := { x | v x ≤ 1 },
  one_mem' := le_of_eq v.map_one,
  mul_mem' := λ x y hx hy, trans_rel_right (≤) (v.map_mul x y) (mul_le_one' hx hy),
  zero_mem' := trans_rel_right (≤) v.map_zero zero_le_one',
  add_mem' := λ x y hx hy, le_trans (v.map_add x y) (max_le hx hy),
  neg_mem' := λ x hx, trans_rel_right (≤) (v.map_neg x) hx }

end ring

section comm_ring

variables {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀]
variables (v : valuation R Γ₀)
variables (O : Type w) [comm_ring O] [algebra O R]

/-- Given a valuation v : R → Γ₀ and a ring homomorphism O →+* R, we say that O is the integers of v
if f is injective, and its range is exactly `v.integer`. -/
structure integers : Prop :=
(hom_inj : function.injective (algebra_map O R))
(map_le_one : ∀ x, v (algebra_map O R x) ≤ 1)
(exists_of_le_one : ∀ ⦃r⦄, v r ≤ 1 → ∃ x, algebra_map O R x = r)

-- typeclass shortcut
instance : algebra v.integer R :=
algebra.of_subring v.integer

theorem integer.integers : v.integers v.integer :=
{ hom_inj := subtype.coe_injective,
  map_le_one := λ r, r.2,
  exists_of_le_one := λ r hr, ⟨⟨r, hr⟩, rfl⟩ }

namespace integers

variables {v O} (hv : integers v O)
include hv

lemma one_of_is_unit {x : O} (hx : is_unit x) : v (algebra_map O R x) = 1 :=
let ⟨u, hu⟩ := hx in le_antisymm (hv.2 _) $
by { rw [← v.map_one, ← (algebra_map O R).map_one, ← u.mul_inv, ← mul_one (v (algebra_map O R x)),
  hu, (algebra_map O R).map_mul, v.map_mul], exact mul_le_mul_left' (hv.2 (u⁻¹ : units O)) _ }

lemma is_unit_of_one {x : O} (hx : is_unit (algebra_map O R x)) (hvx : v (algebra_map O R x) = 1) :
  is_unit x :=
let ⟨u, hu⟩ := hx in
have h1 : v u ≤ 1, from hu.symm ▸ hv.2 x,
have h2 : v (u⁻¹ : units R) ≤ 1,
  by rw [← one_mul (v _), ← hvx, ← v.map_mul, ← hu, u.mul_inv, hu, hvx, v.map_one],
let ⟨r1, hr1⟩ := hv.3 h1, ⟨r2, hr2⟩ := hv.3 h2 in
⟨⟨r1, r2, hv.1 $ by rw [ring_hom.map_mul, ring_hom.map_one, hr1, hr2, units.mul_inv],
  hv.1 $ by rw [ring_hom.map_mul, ring_hom.map_one, hr1, hr2, units.inv_mul]⟩,
hv.1 $ hr1.trans hu⟩

lemma le_of_dvd {x y : O} (h : x ∣ y) : v (algebra_map O R y) ≤ v (algebra_map O R x) :=
let ⟨z, hz⟩ := h in by { rw [← mul_one (v (algebra_map O R x)), hz, ring_hom.map_mul, v.map_mul],
  exact mul_le_mul_left' (hv.2 z) _ }

end integers

end comm_ring

section field

variables {F : Type u} {Γ₀ : Type v} [field F] [linear_ordered_comm_group_with_zero Γ₀]
variables {v : valuation F Γ₀} {O : Type w} [comm_ring O] [algebra O F] (hv : integers v O)
include hv

namespace integers

lemma dvd_of_le {x y : O} (h : v (algebra_map O F x) ≤ v (algebra_map O F y)) : y ∣ x :=
classical.by_cases (λ hy : algebra_map O F y = 0, have hx : x = 0,
    from hv.1 $ (algebra_map O F).map_zero.symm ▸
      (v.zero_iff.1 $ le_zero_iff.1 (v.map_zero ▸ hy ▸ h)),
  hx.symm ▸ dvd_zero y) $
λ hy : algebra_map O F y ≠ 0,
have v ((algebra_map O F y)⁻¹ * algebra_map O F x) ≤ 1,
  by { rw [← v.map_one, ← inv_mul_cancel hy, v.map_mul, v.map_mul], exact mul_le_mul_left' h _ },
let ⟨z, hz⟩ := hv.3 this in
⟨z, hv.1 $ ((algebra_map O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩

lemma dvd_iff_le {x y : O} : x ∣ y ↔ v (algebra_map O F y) ≤ v (algebra_map O F x) :=
⟨hv.le_of_dvd, hv.dvd_of_le⟩

lemma le_iff_dvd {x y : O} : v (algebra_map O F x) ≤ v (algebra_map O F y) ↔ y ∣ x :=
⟨hv.dvd_of_le, hv.le_of_dvd⟩

end integers

end field

end valuation
