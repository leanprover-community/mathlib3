/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import algebra.group.with_one.basic
import algebra.group_with_zero.units.basic

/-!
# Isomorphism between a group and the units of itself adjoined with `0`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Notes
This is here to keep `algebra.group_with_zero.units.basic` out of the import requirements of
`algebra.order.field.defs`.
-/

namespace with_zero

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
def units_with_zero_equiv {α : Type*} [group α] : (with_zero α)ˣ ≃* α :=
{ to_fun    := λ a, unzero a.ne_zero,
  inv_fun   := λ a, units.mk0 a coe_ne_zero,
  left_inv  := λ _, units.ext $ by simpa only [coe_unzero],
  right_inv := λ _, rfl,
  map_mul'  := λ _ _, coe_inj.mp $ by simpa only [coe_unzero, coe_mul] }

end with_zero
