/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import group_theory.group_action.defs
/-!
# Prod instances for additive and multiplicative actions

This file defines instances for binary product of additive and multiplicative actions
-/

variables {M N α β : Type*}

namespace prod

section

variables [has_scalar M α] [has_scalar M β] [has_scalar N α] [has_scalar N β] (a : M) (x : α × β)

@[to_additive prod.has_vadd] instance : has_scalar M (α × β) := ⟨λa p, (a • p.1, a • p.2)⟩

@[simp, to_additive] theorem smul_fst : (a • x).1 = a • x.1 := rfl
@[simp, to_additive] theorem smul_snd : (a • x).2 = a • x.2 := rfl
@[simp, to_additive] theorem smul_mk (a : M) (b : α) (c : β) : a • (b, c) = (a • b, a • c) := rfl

instance [has_scalar M N] [is_scalar_tower M N α] [is_scalar_tower M N β] :
  is_scalar_tower M N (α × β) :=
⟨λ x y z, mk.inj_iff.mpr ⟨smul_assoc _ _ _, smul_assoc _ _ _⟩⟩

@[to_additive] instance [smul_comm_class M N α] [smul_comm_class M N β] :
  smul_comm_class M N (α × β) :=
{ smul_comm := λ r s x, mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩ }

end

@[to_additive] instance {m : monoid M} [mul_action M α] [mul_action M β] : mul_action M (α × β) :=
{ mul_smul  := λ a₁ a₂ p, mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩,
  one_smul  := λ ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩ }

end prod
