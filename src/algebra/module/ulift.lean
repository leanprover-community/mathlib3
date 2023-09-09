/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.ring.ulift
import algebra.module.equiv

/-!
# `ulift` instances for module and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for module, mul_action and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.module_equiv : ulift M ≃ₗ[R] M`.

-/

namespace ulift
universes u v w
variable {R : Type u}
variable {M : Type v}
variable {N : Type w}

@[to_additive]
instance has_smul_left [has_smul R M] :
  has_smul (ulift R) M :=
⟨λ s x, s.down • x⟩

@[simp, to_additive]
lemma smul_def [has_smul R M] (s : ulift R) (x : M) : s • x = s.down • x := rfl

instance is_scalar_tower [has_smul R M] [has_smul M N] [has_smul R N]
  [is_scalar_tower R M N] : is_scalar_tower (ulift R) M N :=
⟨λ x y z, show (x.down • y) • z = x.down • y • z, from smul_assoc _ _ _⟩

instance is_scalar_tower' [has_smul R M] [has_smul M N] [has_smul R N]
  [is_scalar_tower R M N] : is_scalar_tower R (ulift M) N :=
⟨λ x y z, show (x • y.down) • z = x • y.down • z, from smul_assoc _ _ _⟩

instance is_scalar_tower'' [has_smul R M] [has_smul M N] [has_smul R N]
  [is_scalar_tower R M N] : is_scalar_tower R M (ulift N) :=
⟨λ x y z, show up ((x • y) • z.down) = ⟨x • y • z.down⟩, by rw smul_assoc⟩

instance [has_smul R M] [has_smul Rᵐᵒᵖ M] [is_central_scalar R M] :
  is_central_scalar R (ulift M) :=
⟨λ r m, congr_arg up $ op_smul_eq_smul r m.down⟩

@[to_additive]
instance mul_action [monoid R] [mul_action R M] : mul_action (ulift R) M :=
{ smul := (•),
  mul_smul := λ _ _, mul_smul _ _,
  one_smul := one_smul _ }

@[to_additive]
instance mul_action' [monoid R] [mul_action R M] :
  mul_action R (ulift M) :=
{ smul := (•),
  mul_smul := λ r s ⟨f⟩, ext _ _ $ mul_smul _ _ _,
  one_smul := λ ⟨f⟩, ext _ _ $ one_smul _ _ }

instance smul_zero_class [has_zero M] [smul_zero_class R M] :
  smul_zero_class (ulift R) M :=
{ smul_zero := λ _, smul_zero _,
  .. ulift.has_smul_left }

instance smul_zero_class' [has_zero M] [smul_zero_class R M] :
  smul_zero_class R (ulift M) :=
{ smul_zero := λ c, by { ext, simp [smul_zero], } }

instance distrib_smul [add_zero_class M] [distrib_smul R M] :
  distrib_smul (ulift R) M :=
{ smul_add := λ _, smul_add _ }

instance distrib_smul' [add_zero_class M] [distrib_smul R M] :
  distrib_smul R (ulift M) :=
{ smul_add := λ c f g, by { ext, simp [smul_add], } }

instance distrib_mul_action [monoid R] [add_monoid M] [distrib_mul_action R M] :
  distrib_mul_action (ulift R) M :=
{ ..ulift.mul_action,
  ..ulift.distrib_smul }

instance distrib_mul_action' [monoid R] [add_monoid M] [distrib_mul_action R M] :
  distrib_mul_action R (ulift M) :=
{ ..ulift.mul_action',
  ..ulift.distrib_smul' }

instance mul_distrib_mul_action [monoid R] [monoid M] [mul_distrib_mul_action R M] :
  mul_distrib_mul_action (ulift R) M :=
{ smul_one := λ _, smul_one _,
  smul_mul := λ _, smul_mul' _ }

instance mul_distrib_mul_action' [monoid R] [monoid M] [mul_distrib_mul_action R M] :
  mul_distrib_mul_action R (ulift M) :=
{ smul_one := λ _, by { ext, simp [smul_one], },
  smul_mul := λ c f g, by { ext, simp [smul_mul'], },
  ..ulift.mul_action' }

instance smul_with_zero [has_zero R] [has_zero M] [smul_with_zero R M] :
  smul_with_zero (ulift R) M :=
{ smul_zero := λ _, smul_zero _,
  zero_smul := zero_smul _,
  ..ulift.has_smul_left }

instance smul_with_zero' [has_zero R] [has_zero M] [smul_with_zero R M] :
  smul_with_zero R (ulift M) :=
{ smul_zero := λ _, ulift.ext _ _ $ smul_zero _,
  zero_smul := λ _, ulift.ext _ _ $ zero_smul _ _ }

instance mul_action_with_zero [monoid_with_zero R] [has_zero M] [mul_action_with_zero R M] :
  mul_action_with_zero (ulift R) M :=
{ ..ulift.smul_with_zero }

instance mul_action_with_zero' [monoid_with_zero R] [has_zero M] [mul_action_with_zero R M] :
  mul_action_with_zero R (ulift M) :=
{ ..ulift.smul_with_zero' }

instance module [semiring R] [add_comm_monoid M] [module R M] : module (ulift R) M :=
{ add_smul := λ _ _, add_smul _ _,
  ..ulift.smul_with_zero }

instance module' [semiring R] [add_comm_monoid M] [module R M] : module R (ulift M) :=
{ add_smul := λ _ _ _, ulift.ext _ _ $ add_smul _ _ _,
  ..ulift.smul_with_zero' }

/--
The `R`-linear equivalence between `ulift M` and `M`.
-/
@[simps apply symm_apply]
def module_equiv [semiring R] [add_comm_monoid M] [module R M] : ulift M ≃ₗ[R] M :=
{ to_fun := ulift.down,
  inv_fun := ulift.up,
  map_smul' := λ r x, rfl,
  map_add' := λ x y, rfl,
  left_inv := by tidy,
  right_inv := by tidy, }

end ulift
