/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import group_theory.group_action.defs

/-!
# Sum instances for additive and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for additive and multiplicative actions on the binary `sum` type.

## See also

* `group_theory.group_action.option`
* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
-/

variables {M N P α β γ : Type*}

namespace sum

section has_smul
variables [has_smul M α] [has_smul M β] [has_smul N α] [has_smul N β] (a : M) (b : α)
  (c : β) (x : α ⊕ β)

@[to_additive sum.has_vadd] instance : has_smul M (α ⊕ β) := ⟨λ a, sum.map ((•) a) ((•) a)⟩

@[to_additive] lemma smul_def : a • x = x.map ((•) a) ((•) a) := rfl
@[simp, to_additive] lemma smul_inl : a • (inl b : α ⊕ β) = inl (a • b) := rfl
@[simp, to_additive] lemma smul_inr : a • (inr c : α ⊕ β) = inr (a • c) := rfl
@[simp, to_additive] lemma smul_swap : (a • x).swap = a • x.swap := by cases x; refl

instance [has_smul M N] [is_scalar_tower M N α] [is_scalar_tower M N β] :
  is_scalar_tower M N (α ⊕ β) :=
⟨λ a b x,
  by { cases x, exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)] }⟩

@[to_additive] instance [smul_comm_class M N α] [smul_comm_class M N β] :
  smul_comm_class M N (α ⊕ β) :=
⟨λ a b x,
  by { cases x, exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)] }⟩

@[to_additive]
instance [has_smul Mᵐᵒᵖ α] [has_smul Mᵐᵒᵖ β] [is_central_scalar M α] [is_central_scalar M β] :
  is_central_scalar M (α ⊕ β) :=
⟨λ a x,
  by { cases x, exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)] }⟩

@[to_additive] instance has_faithful_smul_left [has_faithful_smul M α] :
  has_faithful_smul M (α ⊕ β) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ a : α, by injection h (inl a)⟩

@[to_additive] instance has_faithful_smul_right [has_faithful_smul M β] :
  has_faithful_smul M (α ⊕ β) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ b : β, by injection h (inr b)⟩

end has_smul

@[to_additive] instance {m : monoid M} [mul_action M α] [mul_action M β] : mul_action M (α ⊕ β) :=
{ mul_smul := λ a b x,
    by { cases x, exacts [congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)] },
  one_smul := λ x,
    by { cases x, exacts [congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)] } }

end sum
