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

variables {R : Type*} {S : Type*} {M : Type*} {N : Type*}

namespace prod

instance [has_scalar R M] [has_scalar R N] : has_scalar R (M × N) := ⟨λa p, (a • p.1, a • p.2)⟩

@[simp] theorem smul_fst [has_scalar R M] [has_scalar R N]
  (a : R) (x : M × N) : (a • x).1 = a • x.1 := rfl
@[simp] theorem smul_snd [has_scalar R M] [has_scalar R N]
  (a : R) (x : M × N) : (a • x).2 = a • x.2 := rfl
@[simp] theorem smul_mk [has_scalar R M] [has_scalar R N]
  (a : R) (b : M) (c : N) : a • (b, c) = (a • b, a • c) := rfl

instance {r : semiring R} [add_comm_monoid M] [add_comm_monoid N]
  [semimodule R M] [semimodule R N] : semimodule R (M × N) :=
{ smul_add  := assume a p₁ p₂, mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩,
  add_smul  := assume a p₁ p₂, mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩,
  mul_smul  := assume a₁ a₂ p, mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩,
  one_smul  := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩,
  zero_smul := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩,
  smul_zero := assume a, mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩,
  .. prod.has_scalar }

instance {r : semiring R} {s : semiring S} [add_comm_monoid M] [add_comm_monoid N]
  [semimodule R M] [semimodule R N] [semimodule S M] [semimodule S N]
  [smul_comm_class R S M] [smul_comm_class R S N] :
  smul_comm_class R S (M × N) :=
{ smul_comm := λ r s x, mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩ }

end prod
