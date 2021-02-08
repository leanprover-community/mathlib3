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

variables {α β γ M N M₂ R S : Type*}

namespace prod

section

variables [has_scalar M α] [has_scalar M β]

instance : has_scalar M (α × β) := ⟨λa p, (a • p.1, a • p.2)⟩

@[simp] theorem smul_fst (c : M) (p : α × β) : (c • p).1 = c • p.1 := rfl
@[simp] theorem smul_snd (c : M) (p : α × β) : (c • p).2 = c • p.2 := rfl
@[simp] theorem smul_mk (c : M) (a : α) (b : β) : c • (a, b) = (c • a, c • b) := rfl

variables [has_scalar N α] [has_scalar N β]

instance [smul_comm_class M N α] [smul_comm_class M N β] :
  smul_comm_class M N (α × β) :=
⟨λ m n ⟨a, b⟩, by simp only [smul_mk, smul_comm m n]⟩

instance [has_scalar M N] [is_scalar_tower M N α] [is_scalar_tower M N β] :
  is_scalar_tower M N (α × β) :=
⟨λ m n ⟨a, b⟩, by simp only [smul_mk, smul_assoc]⟩

end

instance {_ : monoid M} [mul_action M α] [mul_action M β] : mul_action M (α × β) :=
{ one_smul := λ ⟨a, b⟩, by rw [smul_mk, one_smul, one_smul],
  mul_smul := λ c₁ c₂ ⟨a, b⟩, by simp only [smul_mk, mul_smul] }

instance {_ : monoid N} {_ : add_comm_monoid M} {_ : add_comm_monoid M₂}
  [distrib_mul_action N M] [distrib_mul_action N M₂] :
  distrib_mul_action N (M × M₂) :=
{ smul_add  := assume a p₁ p₂, mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩,
  smul_zero := assume a, mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩ }

instance {_ : semiring R} [add_comm_monoid M] [add_comm_monoid M₂]
  [semimodule R M] [semimodule R M₂] : semimodule R (M × M₂) :=
{ add_smul  := assume a p₁ p₂, mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩,
  zero_smul := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩ }

end prod
