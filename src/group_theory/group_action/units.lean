/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.group_action.defs

/-! # Group actions on and by `units M`

This file provides the action of a unit on a type `α`, `has_scalar (units M) α`, in the presence of
`has_scalar M α`, with the obvious definition stated in `units.smul_def`. This definition preserves
`mul_action` and `distrib_mul_action` structures too.

Additionally, a `mul_action G M` for some group `G` satisfying some additional properties admits a
`mul_action G (units M)` structure, again with the obvious definition stated in `units.coe_smul`.
These instances use a primed name.

The results are repeated for `add_units` and `has_vadd` where relevant.
-/

variables {G H M N : Type*} {α : Type*}

namespace units

/-! ### Action of the units of `M` on a type `α` -/

@[to_additive]
instance [monoid M] [has_scalar M α] : has_scalar (units M) α :=
{ smul := λ m a, (m : M) • a }

@[to_additive]
lemma smul_def [monoid M] [has_scalar M α] (m : units M) (a : α) :
  m • a = (m : M) • a := rfl

@[to_additive]
instance [monoid M] [has_scalar M α] [has_faithful_scalar M α] : has_faithful_scalar (units M) α :=
{ eq_of_smul_eq_smul := λ u₁ u₂ h, units.ext $ eq_of_smul_eq_smul h, }

@[to_additive]
instance [monoid M] [mul_action M α] : mul_action (units M) α :=
{ one_smul := (one_smul M : _),
  mul_smul := λ m n, mul_smul (m : M) n, }

instance [monoid M] [add_monoid α] [distrib_mul_action M α] : distrib_mul_action (units M) α :=
{ smul_add := λ m, smul_add (m : M),
  smul_zero := λ m, smul_zero m, }

instance smul_comm_class_left [monoid M] [has_scalar M α] [has_scalar N α]
  [smul_comm_class M N α] : smul_comm_class (units M) N α :=
{ smul_comm := λ m n, (smul_comm (m : M) n : _)}

instance smul_comm_class_right [monoid N] [has_scalar M α] [has_scalar N α]
  [smul_comm_class M N α] : smul_comm_class M (units N) α :=
{ smul_comm := λ m n, (smul_comm m (n : N) : _)}

instance [monoid M] [has_scalar M N] [has_scalar M α] [has_scalar N α] [is_scalar_tower M N α] :
  is_scalar_tower (units M) N α :=
{ smul_assoc := λ m n, (smul_assoc (m : M) n : _)}

/-! ### Action of a group `G` on units of `M` -/

/-- If an action `G` associates and commutes with multiplication on `M`, then it lifts to an
action on `units M`. Notably, this provides `mul_action (units M) (units N)` under suitable
conditions.
-/
instance mul_action' [group G] [monoid M] [mul_action G M] [smul_comm_class G M M]
  [is_scalar_tower G M M] : mul_action G (units M) :=
{ smul := λ g m, ⟨g • (m : M), g⁻¹ • ↑(m⁻¹),
    by rw [smul_mul_smul, units.mul_inv, mul_right_inv, one_smul],
    by rw [smul_mul_smul, units.inv_mul, mul_left_inv, one_smul]⟩,
  one_smul := λ m, units.ext $ one_smul _ _,
  mul_smul := λ g₁ g₂ m, units.ext $ mul_smul _ _ _ }

@[simp] lemma coe_smul [group G] [monoid M] [mul_action G M] [smul_comm_class G M M]
  [is_scalar_tower G M M] (g : G) (m : units M) : ↑(g • m) = g • (m : M) := rfl

/-- Note that this lemma exists more generally as the global `smul_inv` -/
@[simp] lemma smul_inv [group G] [monoid M] [mul_action G M] [smul_comm_class G M M]
  [is_scalar_tower G M M] (g : G) (m : units M) : (g • m)⁻¹ = g⁻¹ • m⁻¹ := ext rfl

/-- Transfer `smul_comm_class G H M` to `smul_comm_class G H (units M)` -/
instance smul_comm_class' [group G] [group H] [monoid M]
  [mul_action G M] [smul_comm_class G M M]
  [mul_action H M] [smul_comm_class H M M]
  [is_scalar_tower G M M] [is_scalar_tower H M M]
  [smul_comm_class G H M] : smul_comm_class G H (units M) :=
{ smul_comm := λ g h m, units.ext $ smul_comm g h (m : M) }

/-- Transfer `is_scalar_tower G H M` to `is_scalar_tower G H (units M)` -/
instance is_scalar_tower' [has_scalar G H] [group G] [group H] [monoid M]
  [mul_action G M] [smul_comm_class G M M]
  [mul_action H M] [smul_comm_class H M M]
  [is_scalar_tower G M M] [is_scalar_tower H M M]
  [is_scalar_tower G H M] : is_scalar_tower G H (units M) :=
{ smul_assoc := λ g h m, units.ext $ smul_assoc g h (m : M) }

/-- Transfer `is_scalar_tower G M α` to `is_scalar_tower G (units M) α` -/
instance is_scalar_tower'_left [group G] [monoid M] [mul_action G M] [has_scalar M α]
  [has_scalar G α] [smul_comm_class G M M] [is_scalar_tower G M M]
  [is_scalar_tower G M α] :
  is_scalar_tower G (units M) α :=
{ smul_assoc := λ g m, (smul_assoc g (m : M) : _)}

-- Just to prove this transfers a particularly useful instance.
example [monoid M] [monoid N] [mul_action M N] [smul_comm_class M N N]
  [is_scalar_tower M N N] : mul_action (units M) (units N) := units.mul_action'

end units
