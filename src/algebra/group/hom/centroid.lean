/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.ring.basic

/-!
# Centroid homomorphisms

This file defines centroid homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `centroid_hom`: Maps which preserve `⊔`.

## Typeclasses

* `centroid_hom_class`
-/

open function

variables {F α : Type*}

/-- The type of centroid homomorphisms from `α` to `α`. -/
structure centroid_hom (α : Type*) [non_unital_non_assoc_semiring α] extends α →+ α :=
(map_mul_left' (a b : α) : to_fun (a * b) = a * to_fun b)
(map_mul_right' (a b : α) : to_fun (a * b) = to_fun a * b)

/-- `centroid_hom_class F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `centroid_hom`. -/
class centroid_hom_class (F : Type*) (α : out_param $ Type*) [non_unital_non_assoc_semiring α]
  extends add_monoid_hom_class F α α :=
(map_mul_left (f : F) (a b : α) : f (a * b) = a * f b)
(map_mul_right (f : F) (a b : α) : f (a * b) = f a * b)

export centroid_hom_class (map_mul_left map_mul_right)

instance [non_unital_non_assoc_semiring α] [centroid_hom_class F α] :
  has_coe_t F (centroid_hom α) :=
⟨λ f, { to_fun := f, map_mul_left' := map_mul_left f, map_mul_right' := map_mul_right f,
  ..(f : α →+ α) }⟩

/-! ### Centroid homomorphisms -/

namespace centroid_hom
variables [non_unital_non_assoc_semiring α]

instance : centroid_hom_class (centroid_hom α) α :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_zero := λ f, f.map_zero',
  map_add := λ f, f.map_add',
  map_mul_left := λ f, f.map_mul_left',
  map_mul_right := λ f, f.map_mul_right' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (centroid_hom α) (λ _, α → α) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : centroid_hom α} : f.to_fun = (f : α → α) := rfl

@[ext] lemma ext {f g : centroid_hom α} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `centroid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : centroid_hom α) (f' : α → α) (h : f' = f) :
  centroid_hom α :=
{ to_fun := f',
  map_mul_left' := λ a b, by simp_rw [h, map_mul_left],
  map_mul_right' := λ a b, by simp_rw [h, map_mul_right],
  ..f.to_add_monoid_hom.copy f' $ by exact h }

variables (α)

/-- `id` as a `centroid_hom`. -/
protected def id : centroid_hom α := ⟨add_monoid_hom.id α, λ _ _, rfl, λ _ _, rfl⟩

instance : inhabited (centroid_hom α) := ⟨centroid_hom.id α⟩

@[simp] lemma coe_id : ⇑(centroid_hom.id α) = id := rfl

lemma coe_to_add_monoid_hom_id : (centroid_hom.id α : α →+ α) = add_monoid_hom.id α := rfl

variables {α}

@[simp] lemma id_apply (a : α) : centroid_hom.id α a = a := rfl

/-- Composition of `centroid_hom`s as a `centroid_hom`. -/
def comp (g f : centroid_hom α) : centroid_hom α :=
⟨g.to_add_monoid_hom.comp f.to_add_monoid_hom,
  λ a b, (congr_arg g $ f.map_mul_left' _ _).trans $ g.map_mul_left' _ _,
  λ a b, (congr_arg g $ f.map_mul_right' _ _).trans $ g.map_mul_right' _ _⟩

@[simp] lemma coe_comp (g f : centroid_hom α) : ⇑(g.comp f) = g ∘ f := rfl
@[simp] lemma comp_apply (g f : centroid_hom α) (a : α) : g.comp f a = g (f a) := rfl
@[simp] lemma coe_comp_add_monoid_hom (g f : centroid_hom α) :
  (g.comp f : α →+ α) = (g : α →+ α).comp f := rfl
@[simp] lemma comp_assoc (h g f : centroid_hom α) : (h.comp g).comp f = h.comp (g.comp f) := rfl
@[simp] lemma comp_id (f : centroid_hom α) : f.comp (centroid_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : centroid_hom α) : (centroid_hom.id α).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ f : centroid_hom α} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g f₁ f₂ : centroid_hom α} (hg : injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end centroid_hom
