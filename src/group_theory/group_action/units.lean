/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.group_action.defs

/-! # Group actions on and by `Mˣ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the action of a unit on a type `α`, `has_smul Mˣ α`, in the presence of
`has_smul M α`, with the obvious definition stated in `units.smul_def`. This definition preserves
`mul_action` and `distrib_mul_action` structures too.

Additionally, a `mul_action G M` for some group `G` satisfying some additional properties admits a
`mul_action G Mˣ` structure, again with the obvious definition stated in `units.coe_smul`.
These instances use a primed name.

The results are repeated for `add_units` and `has_vadd` where relevant.
-/

variables {G H M N : Type*} {α : Type*}

namespace units

/-! ### Action of the units of `M` on a type `α` -/

@[to_additive]
instance [monoid M] [has_smul M α] : has_smul Mˣ α :=
{ smul := λ m a, (m : M) • a }

@[to_additive]
lemma smul_def [monoid M] [has_smul M α] (m : Mˣ) (a : α) :
  m • a = (m : M) • a := rfl

@[simp] lemma smul_is_unit [monoid M] [has_smul M α] {m : M} (hm : is_unit m) (a : α) :
  hm.unit • a = m • a :=
rfl

lemma _root_.is_unit.inv_smul [monoid α] {a : α} (h : is_unit a) :
  (h.unit)⁻¹ • a = 1 :=
h.coe_inv_mul

@[to_additive]
instance [monoid M] [has_smul M α] [has_faithful_smul M α] : has_faithful_smul Mˣ α :=
{ eq_of_smul_eq_smul := λ u₁ u₂ h, units.ext $ eq_of_smul_eq_smul h, }

@[to_additive]
instance [monoid M] [mul_action M α] : mul_action Mˣ α :=
{ one_smul := (one_smul M : _),
  mul_smul := λ m n, mul_smul (m : M) n, }

instance [monoid M] [has_zero α] [smul_zero_class M α] : smul_zero_class Mˣ α :=
{ smul := (•),
  smul_zero := λ m, smul_zero m }

instance [monoid M] [add_zero_class α] [distrib_smul M α] : distrib_smul Mˣ α :=
{ smul_add := λ m, smul_add (m : M) }

instance [monoid M] [add_monoid α] [distrib_mul_action M α] : distrib_mul_action Mˣ α :=
{ .. units.distrib_smul }

instance [monoid M] [monoid α] [mul_distrib_mul_action M α] : mul_distrib_mul_action Mˣ α :=
{ smul_mul := λ m, smul_mul' (m : M),
  smul_one := λ m, smul_one m, }

instance smul_comm_class_left [monoid M] [has_smul M α] [has_smul N α]
  [smul_comm_class M N α] : smul_comm_class Mˣ N α :=
{ smul_comm := λ m n, (smul_comm (m : M) n : _)}

instance smul_comm_class_right [monoid N] [has_smul M α] [has_smul N α]
  [smul_comm_class M N α] : smul_comm_class M Nˣ α :=
{ smul_comm := λ m n, (smul_comm m (n : N) : _)}

instance [monoid M] [has_smul M N] [has_smul M α] [has_smul N α] [is_scalar_tower M N α] :
  is_scalar_tower Mˣ N α :=
{ smul_assoc := λ m n, (smul_assoc (m : M) n : _)}

/-! ### Action of a group `G` on units of `M` -/

/-- If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
action on `Mˣ`. Notably, this provides `mul_action Mˣ Nˣ` under suitable
conditions.
-/
instance mul_action' [group G] [monoid M] [mul_action G M] [smul_comm_class G M M]
  [is_scalar_tower G M M] : mul_action G Mˣ :=
{ smul := λ g m, ⟨g • (m : M), g⁻¹ • ↑(m⁻¹),
    by rw [smul_mul_smul, units.mul_inv, mul_right_inv, one_smul],
    by rw [smul_mul_smul, units.inv_mul, mul_left_inv, one_smul]⟩,
  one_smul := λ m, units.ext $ one_smul _ _,
  mul_smul := λ g₁ g₂ m, units.ext $ mul_smul _ _ _ }

@[simp] lemma coe_smul [group G] [monoid M] [mul_action G M] [smul_comm_class G M M]
  [is_scalar_tower G M M] (g : G) (m : Mˣ) : ↑(g • m) = g • (m : M) := rfl

/-- Note that this lemma exists more generally as the global `smul_inv` -/
@[simp] lemma smul_inv [group G] [monoid M] [mul_action G M] [smul_comm_class G M M]
  [is_scalar_tower G M M] (g : G) (m : Mˣ) : (g • m)⁻¹ = g⁻¹ • m⁻¹ := ext rfl

/-- Transfer `smul_comm_class G H M` to `smul_comm_class G H Mˣ` -/
instance smul_comm_class' [group G] [group H] [monoid M]
  [mul_action G M] [smul_comm_class G M M]
  [mul_action H M] [smul_comm_class H M M]
  [is_scalar_tower G M M] [is_scalar_tower H M M]
  [smul_comm_class G H M] : smul_comm_class G H Mˣ :=
{ smul_comm := λ g h m, units.ext $ smul_comm g h (m : M) }

/-- Transfer `is_scalar_tower G H M` to `is_scalar_tower G H Mˣ` -/
instance is_scalar_tower' [has_smul G H] [group G] [group H] [monoid M]
  [mul_action G M] [smul_comm_class G M M]
  [mul_action H M] [smul_comm_class H M M]
  [is_scalar_tower G M M] [is_scalar_tower H M M]
  [is_scalar_tower G H M] : is_scalar_tower G H Mˣ :=
{ smul_assoc := λ g h m, units.ext $ smul_assoc g h (m : M) }

/-- Transfer `is_scalar_tower G M α` to `is_scalar_tower G Mˣ α` -/
instance is_scalar_tower'_left [group G] [monoid M] [mul_action G M] [has_smul M α]
  [has_smul G α] [smul_comm_class G M M] [is_scalar_tower G M M]
  [is_scalar_tower G M α] :
  is_scalar_tower G Mˣ α :=
{ smul_assoc := λ g m, (smul_assoc g (m : M) : _)}

-- Just to prove this transfers a particularly useful instance.
example [monoid M] [monoid N] [mul_action M N] [smul_comm_class M N N]
  [is_scalar_tower M N N] : mul_action Mˣ Nˣ := units.mul_action'

/-- A stronger form of `units.mul_action'`. -/
instance mul_distrib_mul_action' [group G] [monoid M] [mul_distrib_mul_action G M]
  [smul_comm_class G M M] [is_scalar_tower G M M] : mul_distrib_mul_action G Mˣ :=
{ smul := (•),
  smul_one := λ m, units.ext $ smul_one _,
  smul_mul := λ g m₁ m₂, units.ext $ smul_mul' _ _ _,
  .. units.mul_action' }

end units

lemma is_unit.smul [group G] [monoid M] [mul_action G M]
  [smul_comm_class G M M] [is_scalar_tower G M M] {m : M} (g : G) (h : is_unit m) :
  is_unit (g • m) :=
let ⟨u, hu⟩ := h in hu ▸ ⟨g • u, units.coe_smul _ _⟩
