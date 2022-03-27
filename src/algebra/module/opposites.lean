/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.module.equiv
import group_theory.group_action.opposite

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`group_theory.group_action.opposite`.
-/

variables (R M : Type*}

namespace mul_opposite

instance [has_zero R] [has_zero M] [smul_with_zero R M] : smul_with_zero R Mᵐᵒᵖ :=
{ smul_zero := λ r, unop_injective $ smul_zero r,
  zero_smul := λ r, unop_injective $ zero_smul' r }

instance [monoid_with_zero R] [has_zero M] [mul_action_with_zero R M] :
  mul_action_with_zero R Mᵐᵒᵖ :=
{ ..mul_opposite.smul_with_zero M R }

instance [monoid_with_zero R] [add_monoid M] [distrib_mul_action_with_zero R M] :
  distrib_mul_action_with_zero R Mᵐᵒᵖ :=
{ ..mul_opposite.smul_with_zero M R }

variables {M} [semiring R] [add_comm_monoid M] [module R M]

/-- `mul_opposite.distrib_mul_action_with_zero` extends to a `module`. -/
instance : module R (mul_opposite M) :=
{ add_smul := λ r₁ r₂ x, unop_injective $ add_smul r₁ r₂ (unop x) }

/-- The function `op` is a linear equivalence. -/
def op_linear_equiv : M ≃ₗ[R] Mᵐᵒᵖ :=
{ map_smul' := mul_opposite.op_smul, .. op_add_equiv }

@[simp] lemma coe_op_linear_equiv :
  (op_linear_equiv R : M → Mᵐᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm :
  ((op_linear_equiv R).symm : Mᵐᵒᵖ → M) = unop := rfl

@[simp] lemma coe_op_linear_equiv_to_linear_map :
  ((op_linear_equiv R).to_linear_map : M → Mᵐᵒᵖ) = op := rfl
@[simp] lemma coe_op_linear_equiv_symm_to_linear_map :
  ((op_linear_equiv R).symm.to_linear_map : Mᵐᵒᵖ → M) = unop := rfl

@[simp] lemma op_linear_equiv_to_add_equiv :
  (op_linear_equiv R : M ≃ₗ[R] Mᵐᵒᵖ).to_add_equiv = op_add_equiv := rfl
@[simp] lemma op_linear_equiv_symm_to_add_equiv :
  (op_linear_equiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.to_add_equiv = op_add_equiv.symm := rfl

end mul_opposite
