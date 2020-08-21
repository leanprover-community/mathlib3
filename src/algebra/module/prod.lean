/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.module.basic
/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {p q : α × β}

namespace prod

instance [has_scalar α β] [has_scalar α γ] : has_scalar α (β × γ) := ⟨λa p, (a • p.1, a • p.2)⟩

@[simp] theorem smul_fst [has_scalar α β] [has_scalar α γ]
  (a : α) (x : β × γ) : (a • x).1 = a • x.1 := rfl
@[simp] theorem smul_snd [has_scalar α β] [has_scalar α γ]
  (a : α) (x : β × γ) : (a • x).2 = a • x.2 := rfl
@[simp] theorem smul_mk [has_scalar α β] [has_scalar α γ]
  (a : α) (b : β) (c : γ) : a • (b, c) = (a • b, a • c) := rfl

instance {r : semiring α} [add_comm_monoid β] [add_comm_monoid γ]
  [semimodule α β] [semimodule α γ] : semimodule α (β × γ) :=
{ smul_add  := assume a p₁ p₂, mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩,
  add_smul  := assume a p₁ p₂, mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩,
  mul_smul  := assume a₁ a₂ p, mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩,
  one_smul  := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩,
  zero_smul := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩,
  smul_zero := assume a, mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩,
  .. prod.has_scalar }

end prod
