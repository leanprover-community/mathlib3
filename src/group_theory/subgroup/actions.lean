/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import group_theory.subgroup.basic

/-!
# Actions by `subgroup`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are just copies of the definitions about `submonoid` starting from `submonoid.mul_action`.

## Tags
subgroup, subgroups

-/

namespace subgroup

variables {G : Type*} [group G]
variables {α β : Type*}

/-- The action by a subgroup is the action by the underlying group. -/
@[to_additive /-"The additive action by an add_subgroup is the action by the underlying
add_group. "-/]
instance [mul_action G α] (S : subgroup G) : mul_action S α :=
S.to_submonoid.mul_action

@[to_additive]
lemma smul_def [mul_action G α] {S : subgroup G} (g : S) (m : α) : g • m = (g : G) • m := rfl

@[to_additive]
instance smul_comm_class_left
  [mul_action G β] [has_smul α β] [smul_comm_class G α β] (S : subgroup G) :
  smul_comm_class S α β :=
S.to_submonoid.smul_comm_class_left

@[to_additive]
instance smul_comm_class_right
  [has_smul α β] [mul_action G β] [smul_comm_class α G β] (S : subgroup G) :
  smul_comm_class α S β :=
S.to_submonoid.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S G G` which is needed by `smul_mul_assoc`. -/
instance
  [has_smul α β] [mul_action G α] [mul_action G β] [is_scalar_tower G α β] (S : subgroup G) :
  is_scalar_tower S α β :=
S.to_submonoid.is_scalar_tower

instance [mul_action G α] [has_faithful_smul G α] (S : subgroup G) :
  has_faithful_smul S α :=
S.to_submonoid.has_faithful_smul

/-- The action by a subgroup is the action by the underlying group. -/
instance [add_monoid α] [distrib_mul_action G α] (S : subgroup G) : distrib_mul_action S α :=
S.to_submonoid.distrib_mul_action

/-- The action by a subgroup is the action by the underlying group. -/
instance [monoid α] [mul_distrib_mul_action G α] (S : subgroup G) : mul_distrib_mul_action S α :=
S.to_submonoid.mul_distrib_mul_action

/-- The center of a group acts commutatively on that group. -/
instance center.smul_comm_class_left : smul_comm_class (center G) G G :=
submonoid.center.smul_comm_class_left

/-- The center of a group acts commutatively on that group. -/
instance center.smul_comm_class_right : smul_comm_class G (center G) G :=
submonoid.center.smul_comm_class_right

end subgroup
