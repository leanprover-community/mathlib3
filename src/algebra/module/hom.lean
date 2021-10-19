/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.module.pi

/-!
# Bundled hom instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on bundled `_hom` types.

These are analogous to the instances in `algebra.module.pi`, but for bundled instead of unbundled
functions.
-/

variables {R S A B : Type*}

namespace add_monoid_hom

section
variables [monoid R] [monoid S] [add_monoid A] [add_comm_monoid B]
variables [distrib_mul_action R B] [distrib_mul_action S B]

instance : distrib_mul_action R (A →+ B) :=
{ smul := λ r f,
  { to_fun := r • f,
    map_zero' := by simp,
    map_add' := λ x y, by simp [smul_add] },
  one_smul := λ f, by simp,
  mul_smul := λ r s f, by simp [mul_smul],
  smul_add := λ r f g, ext $ λ x, by simp [smul_add],
  smul_zero := λ r, ext $ λ x, by simp [smul_zero] }

@[simp] lemma coe_smul (r : R) (f : A →+ B) : ⇑(r • f) = r • f := rfl
lemma smul_apply (r : R) (f : A →+ B) (x : A) : (r • f) x = r • f x := rfl

instance [smul_comm_class R S B] : smul_comm_class R S (A →+ B) :=
⟨λ a b f, ext $ λ x, smul_comm _ _ _⟩

instance [has_scalar R S] [is_scalar_tower R S B] : is_scalar_tower R S (A →+ B) :=
⟨λ a b f, ext $ λ x, smul_assoc _ _ _⟩

end

instance [semiring R] [add_monoid A] [add_comm_monoid B] [module R B] :
  module R (A →+ B) :=
{ add_smul := λ r s x, ext $ λ y, by simp [add_smul],
  zero_smul := λ x, ext $ λ y, by simp [zero_smul],
  ..add_monoid_hom.distrib_mul_action }

end add_monoid_hom
