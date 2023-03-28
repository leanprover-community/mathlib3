/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import group_theory.group_action.defs

/-!
# Option instances for additive and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for additive and multiplicative actions on `option` type. Scalar
multiplication is defined by `a • some b = some (a • b)` and `a • none = none`.

## See also

* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/

variables {M N α : Type*}

namespace option

section has_smul
variables [has_smul M α] [has_smul N α] (a : M) (b : α) (x : option α)

@[to_additive option.has_vadd] instance : has_smul M (option α) := ⟨λ a, option.map $ (•) a⟩

@[to_additive] lemma smul_def : a • x = x.map ((•) a) := rfl
@[simp, to_additive] lemma smul_none : a • (none : option α) = none := rfl
@[simp, to_additive] lemma smul_some : a • some b = some (a • b) := rfl

@[to_additive] instance [has_smul M N] [is_scalar_tower M N α] : is_scalar_tower M N (option α) :=
⟨λ a b x, by { cases x, exacts [rfl, congr_arg some (smul_assoc _ _ _)] }⟩

@[to_additive] instance [smul_comm_class M N α] : smul_comm_class M N (option α) :=
⟨λ a b, function.commute.option_map $ smul_comm _ _⟩

@[to_additive]
instance [has_smul Mᵐᵒᵖ α] [is_central_scalar M α] : is_central_scalar M (option α) :=
⟨λ a x, by { cases x, exacts [rfl, congr_arg some (op_smul_eq_smul _ _)] }⟩

@[to_additive] instance [has_faithful_smul M α] : has_faithful_smul M (option α) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ b : α, by injection h (some b)⟩

end has_smul

instance [monoid M] [mul_action M α] : mul_action M (option α) :=
{ smul := (•),
  one_smul := λ b, by { cases b, exacts [rfl, congr_arg some (one_smul _ _)] },
  mul_smul := λ a₁ a₂ b, by { cases b, exacts [rfl, congr_arg some (mul_smul _ _ _)] } }

end option
