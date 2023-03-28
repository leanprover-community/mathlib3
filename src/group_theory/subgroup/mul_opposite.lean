/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich
-/

import group_theory.subgroup.actions

/-!
# Mul-opposite subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Tags
subgroup, subgroups

-/

variables {G : Type*} [group G]

namespace subgroup

/-- A subgroup `H` of `G` determines a subgroup `H.opposite` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive "An additive subgroup `H` of `G` determines an additive subgroup `H.opposite` of the
  opposite additive group `Gᵃᵒᵖ`."]
def opposite : subgroup G ≃ subgroup Gᵐᵒᵖ :=
{ to_fun := λ H, { carrier := mul_opposite.unop ⁻¹' (H : set G),
                   one_mem' := H.one_mem,
                   mul_mem' := λ a b ha hb, H.mul_mem hb ha,
                   inv_mem' := λ a, H.inv_mem },
  inv_fun := λ H, { carrier := mul_opposite.op ⁻¹' (H : set Gᵐᵒᵖ),
                   one_mem' := H.one_mem,
                   mul_mem' := λ a b ha hb, H.mul_mem hb ha,
                   inv_mem' := λ a, H.inv_mem },
  left_inv := λ H, set_like.coe_injective rfl,
  right_inv := λ H, set_like.coe_injective rfl }

/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive "Bijection between an additive subgroup `H` and its opposite.", simps]
def opposite_equiv (H : subgroup G) : H ≃ H.opposite :=
mul_opposite.op_equiv.subtype_equiv $ λ _, iff.rfl

@[to_additive] instance (H : subgroup G) [encodable H] : encodable H.opposite :=
encodable.of_equiv H H.opposite_equiv.symm

@[to_additive] instance (H : subgroup G) [countable H] : countable H.opposite :=
countable.of_equiv H H.opposite_equiv

@[to_additive] lemma smul_opposite_mul {H : subgroup G} (x g : G) (h : H.opposite) :
  h • (g * x) = g * (h • x) :=
begin
  cases h,
  simp [(•), mul_assoc],
end

end subgroup
