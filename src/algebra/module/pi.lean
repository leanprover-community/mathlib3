/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.module.basic
import algebra.regular.smul
import algebra.ring.pi
import group_theory.group_action.pi

/-!
# Pi instances for modules

This file defines instances for module and related structures on Pi Types
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

lemma _root_.is_smul_regular.pi {α : Type*} [Π i, has_scalar α $ f i] {k : α}
  (hk : Π i, is_smul_regular (f i) k) : is_smul_regular (Π i, f i) k :=
λ _ _ h, funext $ λ i, hk i (congr_fun h i : _)

instance smul_with_zero (α) [has_zero α]
  [Π i, has_zero (f i)] [Π i, smul_with_zero α (f i)] :
  smul_with_zero α (Π i, f i) :=
{ smul_zero := λ _, funext $ λ _, smul_zero' (f _) _,
  zero_smul := λ _, funext $ λ _, zero_smul _ _,
  ..pi.has_scalar }

instance smul_with_zero' {g : I → Type*} [Π i, has_zero (g i)]
  [Π i, has_zero (f i)] [Π i, smul_with_zero (g i) (f i)] :
  smul_with_zero (Π i, g i) (Π i, f i) :=
{ smul_zero := λ _, funext $ λ _, smul_zero' (f _) _,
  zero_smul := λ _, funext $ λ _, zero_smul _ _,
  ..pi.has_scalar' }

instance mul_action_with_zero (α) [monoid_with_zero α]
  [Π i, has_zero (f i)] [Π i, mul_action_with_zero α (f i)] :
  mul_action_with_zero α (Π i, f i) :=
{ ..pi.mul_action _,
  ..pi.smul_with_zero _ }

instance mul_action_with_zero' {g : I → Type*} [Π i, monoid_with_zero (g i)]
  [Π i, has_zero (f i)] [Π i, mul_action_with_zero (g i) (f i)] :
  mul_action_with_zero (Π i, g i) (Π i, f i) :=
{ ..pi.mul_action',
  ..pi.smul_with_zero' }

variables (I f)

instance module (α) {r : semiring α} {m : ∀ i, add_comm_monoid $ f i}
  [∀ i, module α $ f i] :
  @module α (Π i : I, f i) r (@pi.add_comm_monoid I f m) :=
{ add_smul := λ c f g, funext $ λ i, add_smul _ _ _,
  zero_smul := λ f, funext $ λ i, zero_smul α _,
  ..pi.distrib_mul_action _ }

/- Extra instance to short-circuit type class resolution.
For unknown reasons, this is necessary for certain inference problems. E.g., for this to succeed:
```lean
example (β X : Type*) [normed_group β] [normed_space ℝ β] : module ℝ (X → β) := by apply_instance
```
See: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/281296989
-/
/-- A special case of `pi.module` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this. -/
instance _root_.function.module (α β : Type*) [semiring α] [add_comm_monoid β] [module α β] :
  module α (I → β) :=
pi.module _ _ _

variables {I f}

instance module' {g : I → Type*} {r : Π i, semiring (f i)} {m : Π i, add_comm_monoid (g i)}
  [Π i, module (f i) (g i)] :
  module (Π i, f i) (Π i, g i) :=
{ add_smul := by { intros, ext1, apply add_smul },
  zero_smul := by { intros, ext1, apply zero_smul } }

instance (α) {r : semiring α} {m : Π i, add_comm_monoid $ f i}
  [Π i, module α $ f i] [∀ i, no_zero_smul_divisors α $ f i] :
  no_zero_smul_divisors α (Π i : I, f i) :=
⟨λ c x h, or_iff_not_imp_left.mpr (λ hc, funext
  (λ i, (smul_eq_zero.mp (congr_fun h i)).resolve_left hc))⟩

end pi
