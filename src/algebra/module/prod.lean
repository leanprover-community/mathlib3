/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
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

instance [has_scalar R S] [has_scalar S M] [has_scalar R M] [has_scalar S N] [has_scalar R N]
  [is_scalar_tower R S M] [is_scalar_tower R S N] : is_scalar_tower R S (M × N) :=
⟨λ x y z, mk.inj_iff.mpr ⟨smul_assoc _ _ _, smul_assoc _ _ _⟩⟩

instance [has_scalar R M] [has_scalar S M] [has_scalar R N] [has_scalar S N]
  [smul_comm_class R S M] [smul_comm_class R S N] :
  smul_comm_class R S (M × N) :=
{ smul_comm := λ r s x, mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩ }

instance {r : monoid R} [mul_action R M] [mul_action R N] : mul_action R (M × N) :=
{ mul_smul  := λ a₁ a₂ p, mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩,
  one_smul  := λ ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩ }

instance {r : monoid R} [add_monoid M] [add_monoid N]
  [distrib_mul_action R M] [distrib_mul_action R N] : distrib_mul_action R (M × N) :=
{ smul_add  := λ a p₁ p₂, mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩,
  smul_zero := λ a, mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩ }

instance {r : semiring R} [add_comm_monoid M] [add_comm_monoid N]
  [semimodule R M] [semimodule R N] : semimodule R (M × N) :=
{ add_smul  := λ a p₁ p₂, mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩,
  zero_smul := λ ⟨b, c⟩, mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩,
  .. prod.distrib_mul_action }

instance {r : semiring R} [add_comm_monoid M] [add_comm_monoid N]
  [semimodule R M] [semimodule R N]
  [no_zero_smul_divisors R M] [no_zero_smul_divisors R N] :
  no_zero_smul_divisors R (M × N) :=
⟨λ c ⟨x, y⟩ h, or_iff_not_imp_left.mpr (λ hc, mk.inj_iff.mpr
  ⟨(smul_eq_zero.mp (congr_arg fst h)).resolve_left hc,
   (smul_eq_zero.mp (congr_arg snd h)).resolve_left hc⟩)⟩

end prod
