/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import linear_algebra.basic
import algebra.ring.ulift

/-!
# `ulift` instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.module_equiv : ulift M ≃ₗ[R] M`.

-/

namespace ulift
universes u v w
variable {R : Type u}
variable {M : Type v}
variable {N : Type w}

instance has_scalar [has_scalar R M] :
  has_scalar (ulift R) M :=
⟨λ s x, s.down • x⟩

@[simp] lemma smul_down [has_scalar R M] (s : ulift R) (x : M) : (s • x) = s.down • x := rfl

instance has_scalar' [has_scalar R M] :
  has_scalar R (ulift M) :=
⟨λ s x, ⟨s • x.down⟩⟩

@[simp]
lemma smul_down' [has_scalar R M] (s : R) (x : ulift M) :
  (s • x).down = s • x.down :=
rfl

instance is_scalar_tower [has_scalar R M] [has_scalar M N] [has_scalar R N]
  [is_scalar_tower R M N] : is_scalar_tower (ulift R) M N :=
⟨λ x y z, show (x.down • y) • z = x.down • y • z, from smul_assoc _ _ _⟩

instance is_scalar_tower' [has_scalar R M] [has_scalar M N] [has_scalar R N]
  [is_scalar_tower R M N] : is_scalar_tower R (ulift M) N :=
⟨λ x y z, show (x • y.down) • z = x • y.down • z, from smul_assoc _ _ _⟩

instance is_scalar_tower'' [has_scalar R M] [has_scalar M N] [has_scalar R N]
  [is_scalar_tower R M N] : is_scalar_tower R M (ulift N) :=
⟨λ x y z, show up ((x • y) • z.down) = ⟨x • y • z.down⟩, by rw smul_assoc⟩

instance mul_action [monoid R] [mul_action R M] :
  mul_action (ulift R) M :=
{ smul := (•),
  mul_smul := λ r s f, by { cases r, cases s, simp [mul_smul], },
  one_smul := λ f, by { simp [one_smul], } }

instance mul_action' [monoid R] [mul_action R M] :
  mul_action R (ulift M) :=
{ smul := (•),
  mul_smul := λ r s f, by { cases f, ext, simp [mul_smul], },
  one_smul := λ f, by { ext, simp [one_smul], } }

instance distrib_mul_action [monoid R] [add_monoid M] [distrib_mul_action R M] :
  distrib_mul_action (ulift R) M :=
{ smul_zero := λ c, by { cases c, simp [smul_zero], },
  smul_add := λ c f g, by { cases c, simp [smul_add], },
  ..ulift.mul_action }

instance distrib_mul_action' [monoid R] [add_monoid M] [distrib_mul_action R M] :
  distrib_mul_action R (ulift M) :=
{ smul_zero := λ c, by { ext, simp [smul_zero], },
  smul_add := λ c f g, by { ext, simp [smul_add], },
  ..ulift.mul_action' }

instance mul_distrib_mul_action [monoid R] [monoid M] [mul_distrib_mul_action R M] :
  mul_distrib_mul_action (ulift R) M :=
{ smul_one := λ c, by { cases c, simp [smul_one], },
  smul_mul := λ c f g, by { cases c, simp [smul_mul'], },
  ..ulift.mul_action }

instance mul_distrib_mul_action' [monoid R] [monoid M] [mul_distrib_mul_action R M] :
  mul_distrib_mul_action R (ulift M) :=
{ smul_one := λ c, by { ext, simp [smul_one], },
  smul_mul := λ c f g, by { ext, simp [smul_mul'], },
  ..ulift.mul_action' }

instance module [semiring R] [add_comm_monoid M] [module R M] :
  module (ulift R) M :=
{ add_smul := λ c f g, by { cases c, simp [add_smul], },
  zero_smul := λ f, by { simp [zero_smul], },
  ..ulift.distrib_mul_action }

instance module' [semiring R] [add_comm_monoid M] [module R M] :
  module R (ulift M) :=
{ add_smul := by { intros, ext1, apply add_smul },
  zero_smul := by { intros, ext1, apply zero_smul } }

/--
The `R`-linear equivalence between `ulift M` and `M`.
-/
def module_equiv [semiring R] [add_comm_monoid M] [module R M] : ulift M ≃ₗ[R] M :=
{ to_fun := ulift.down,
  inv_fun := ulift.up,
  map_smul' := λ r x, rfl,
  map_add' := λ x y, rfl,
  left_inv := by tidy,
  right_inv := by tidy, }

end ulift
