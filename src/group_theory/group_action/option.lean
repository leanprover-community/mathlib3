/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import group_theory.group_action.defs

/-!
# Sum instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on the binary `sum` type.

## See also

* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
-/

variables {M N P α β γ : Type*}

namespace option

section has_smul
variables [has_smul α β] [has_smul α γ] [has_smul β γ] (a : α) (b : β) (x : option β)

@[to_additive option.has_vadd] instance : has_smul α (option β) := ⟨λ a, option.map $ (•) a⟩

@[to_additive] lemma smul_def : a • x = x.map ((•) a) := rfl
@[simp, to_additive] lemma smul_none : a • (none : option β) = none := rfl
@[simp, to_additive] lemma smul_some : a • some b = some (a • b) := rfl

instance [is_scalar_tower α β γ] : is_scalar_tower α β (option γ) :=
⟨λ a b x, by { cases x, exacts [rfl, congr_arg some (smul_assoc _ _ _)] }⟩

@[to_additive] instance {α β γ : Type*} [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α β (option γ) :=
⟨λ a b x, by { cases x, exacts [rfl, congr_arg some (smul_comm _ _ _)] }⟩

instance [has_smul αᵐᵒᵖ β] [is_central_scalar α β] : is_central_scalar α (option β) :=
⟨λ a x, by { cases x, exacts [rfl, congr_arg some (op_smul_eq_smul _ _)] }⟩

@[to_additive] instance [has_faithful_smul α β] : has_faithful_smul α (option β) :=
⟨λ x y h, eq_of_smul_eq_smul $ λ b : β, by injection h (some b)⟩

end has_smul

instance [monoid α] [mul_action α β] : mul_action α (option β) :=
{ smul := (•),
  one_smul := λ b, by { cases b, exacts [rfl, congr_arg some (one_smul _ _)] },
  mul_smul := λ a₁ a₂ b, by { cases b, exacts [rfl, congr_arg some (mul_smul _ _ _)] } }

end option
