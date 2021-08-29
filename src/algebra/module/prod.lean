/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import algebra.module.basic
import group_theory.group_action.prod

/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/

variables {R : Type*} {S : Type*} {M : Type*} {N : Type*}

namespace prod

instance {r : semiring R} [add_comm_monoid M] [add_comm_monoid N]
  [module R M] [module R N] : module R (M × N) :=
{ add_smul  := λ a p₁ p₂, mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩,
  zero_smul := λ ⟨b, c⟩, mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩,
  .. prod.distrib_mul_action }

instance {r : semiring R} [add_comm_monoid M] [add_comm_monoid N]
  [module R M] [module R N]
  [no_zero_smul_divisors R M] [no_zero_smul_divisors R N] :
  no_zero_smul_divisors R (M × N) :=
⟨λ c ⟨x, y⟩ h, or_iff_not_imp_left.mpr (λ hc, mk.inj_iff.mpr
  ⟨(smul_eq_zero.mp (congr_arg fst h)).resolve_left hc,
   (smul_eq_zero.mp (congr_arg snd h)).resolve_left hc⟩)⟩

end prod
