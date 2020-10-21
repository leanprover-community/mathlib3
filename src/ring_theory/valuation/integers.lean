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

universes u v

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
  add_mem' := λ x y hx hy, le_trans (v.map_add x y)
    (by { letI := classical.DLO Γ₀, exact max_le hx hy }),
  neg_mem' := λ x hx, trans_rel_right (≤) (v.map_neg x) hx }

namespace integer

lemma one_of_is_unit (x : v.integer) (hx : is_unit x) : v x = 1 :=
let ⟨u, hu⟩ := hx in le_antisymm x.2 $
by { rw [← v.map_one, ← v.integer.coe_one, ← u.mul_inv, ← mul_one (v x), hu, subring.coe_mul,
    v.map_mul], exact mul_le_mul_left' (↑(u⁻¹ : units v.integer) : v.integer).2 _ }

lemma is_unit_of_one (x : v.integer) (hx : is_unit (x : R)) (hvx : v x = 1) : is_unit x :=
let ⟨u, hu⟩ := hx in ⟨⟨⟨u, hu.symm ▸ x.2⟩, ⟨(u⁻¹ : units R), show v _ ≤ 1,
    by rw [← one_mul (v _), ← hvx, ← v.map_mul, ← hu, u.mul_inv, hu, hvx, v.map_one]⟩,
  subtype.eq u.mul_inv, subtype.eq u.inv_mul⟩, subtype.eq hu⟩

lemma le_of_dvd {x y : v.integer} (h : x ∣ y) : v y ≤ v x :=
let ⟨z, hz⟩ := h in by { rw [← mul_one (v x), hz, subring.coe_mul, v.map_mul],
  exact mul_le_mul_left' z.2 _ }

end integer

end ring

section comm_ring

variables {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀]
variables (v : valuation R Γ₀)

namespace integer

-- typeclass shortcut
instance : algebra v.integer R :=
algebra.of_subring v.integer

end integer

end comm_ring

section field

variables {F : Type u} {Γ₀ : Type v} [field F] [linear_ordered_comm_group_with_zero Γ₀]
variables (v : valuation F Γ₀)

namespace integer

lemma dvd_of_le {x y : v.integer} (h : v x ≤ v y) : y ∣ x :=
classical.by_cases (λ hy : (y : F) = 0, have hx : x = 0,
    from subtype.ext $ v.zero_iff.1 $ le_zero_iff.1 (v.map_zero ▸ hy ▸ h),
  hx.symm ▸ dvd_zero y) $
λ hy : (y : F) ≠ 0, ⟨⟨y⁻¹ * x, show v (y⁻¹ * x) ≤ 1,
  by { rw [← v.map_one, ← inv_mul_cancel hy, v.map_mul, v.map_mul], exact mul_le_mul_left' h _ }⟩,
subtype.ext $ eq.symm $ mul_inv_cancel_left' hy x⟩

lemma dvd_iff_le {x y : v.integer} : x ∣ y ↔ v y ≤ v x :=
⟨le_of_dvd v, dvd_of_le v⟩

lemma le_iff_dvd {x y : v.integer} : v x ≤ v y ↔ y ∣ x :=
⟨dvd_of_le v, le_of_dvd v⟩

end integer

end field

end valuation
