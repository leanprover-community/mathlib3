/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.module.basic
import algebra.ring.pi

/-!
# Pi instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on Pi Types
-/

namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

instance has_scalar {α : Type*} [Π i, has_scalar α $ f i] :
  has_scalar α (Π i : I, f i) :=
⟨λ s x, λ i, s • (x i)⟩

@[simp] lemma smul_apply {α : Type*} [Π i, has_scalar α $ f i] (s : α) : (s • x) i = s • x i := rfl

instance has_scalar' {g : I → Type*} [Π i, has_scalar (f i) (g i)] :
  has_scalar (Π i, f i) (Π i : I, g i) :=
⟨λ s x, λ i, (s i) • (x i)⟩

@[simp]
lemma smul_apply' {g : I → Type*} [∀ i, has_scalar (f i) (g i)] (s : Π i, f i) (x : Π i, g i) :
  (s • x) i = s i • x i :=
rfl

instance is_scalar_tower {α β : Type*}
  [has_scalar α β] [Π i, has_scalar β $ f i] [Π i, has_scalar α $ f i]
  [Π i, is_scalar_tower α β (f i)] : is_scalar_tower α β (Π i : I, f i) :=
⟨λ x y z, funext $ λ i, smul_assoc x y (z i)⟩

instance is_scalar_tower' {g : I → Type*} {α : Type*}
  [Π i, has_scalar α $ f i] [Π i, has_scalar (f i) (g i)] [Π i, has_scalar α $ g i]
  [Π i, is_scalar_tower α (f i) (g i)] : is_scalar_tower α (Π i : I, f i) (Π i : I, g i) :=
⟨λ x y z, funext $ λ i, smul_assoc x (y i) (z i)⟩

instance is_scalar_tower'' {g : I → Type*} {h : I → Type*}
  [Π i, has_scalar (f i) (g i)] [Π i, has_scalar (g i) (h i)] [Π i, has_scalar (f i) (h i)]
  [Π i, is_scalar_tower (f i) (g i) (h i)] : is_scalar_tower (Π i, f i) (Π i, g i) (Π i, h i) :=
⟨λ x y z, funext $ λ i, smul_assoc (x i) (y i) (z i)⟩

instance mul_action (α) {m : monoid α} [Π i, mul_action α $ f i] :
  @mul_action α (Π i : I, f i) m :=
{ smul := (•),
  mul_smul := λ r s f, funext $ λ i, mul_smul _ _ _,
  one_smul := λ f, funext $ λ i, one_smul α _ }

instance mul_action' {g : I → Type*} {m : Π i, monoid (f i)} [Π i, mul_action (f i) (g i)] :
  @mul_action (Π i, f i) (Π i : I, g i) (@pi.monoid I f m) :=
{ smul := (•),
  mul_smul := λ r s f, funext $ λ i, mul_smul _ _ _,
  one_smul := λ f, funext $ λ i, one_smul _ _ }

instance distrib_mul_action (α) {m : monoid α} {n : ∀ i, add_monoid $ f i} [∀ i, distrib_mul_action α $ f i] :
  @distrib_mul_action α (Π i : I, f i) m (@pi.add_monoid I f n) :=
{ smul_zero := λ c, funext $ λ i, smul_zero _,
  smul_add := λ c f g, funext $ λ i, smul_add _ _ _,
  ..pi.mul_action _ }

instance distrib_mul_action' {g : I → Type*} {m : Π i, monoid (f i)} {n : Π i, add_monoid $ g i}
  [Π i, distrib_mul_action (f i) (g i)] :
  @distrib_mul_action (Π i, f i) (Π i : I, g i) (@pi.monoid I f m) (@pi.add_monoid I g n) :=
{ smul_add := by { intros, ext x, apply smul_add },
  smul_zero := by { intros, ext x, apply smul_zero } }

variables (I f)

instance semimodule (α) {r : semiring α} {m : ∀ i, add_comm_monoid $ f i} [∀ i, semimodule α $ f i] :
  @semimodule α (Π i : I, f i) r (@pi.add_comm_monoid I f m) :=
{ add_smul := λ c f g, funext $ λ i, add_smul _ _ _,
  zero_smul := λ f, funext $ λ i, zero_smul α _,
  ..pi.distrib_mul_action _ }

variables {I f}

instance semimodule' {g : I → Type*} {r : Π i, semiring (f i)} {m : Π i, add_comm_monoid (g i)}
  [Π i, semimodule (f i) (g i)] :
  semimodule (Π i, f i) (Π i, g i) :=
{ add_smul := by { intros, ext1, apply add_smul },
  zero_smul := by { intros, ext1, apply zero_smul } }

end pi
