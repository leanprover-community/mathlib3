/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.bounded
import topology.order.hom.basic

/-!
# Esakia morphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pseudo-epimorphisms and Esakia morphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `pseudo_epimorphism`: Pseudo-epimorphisms. Maps `f` such that `f a ≤ b` implies the existence of
  `a'` such that `a ≤ a'` and `f a' = b`.
* `esakia_hom`: Esakia morphisms. Continuous pseudo-epimorphisms.

## Typeclasses

* `pseudo_epimorphism_class`
* `esakia_hom_class`

## References

* [Wikipedia, *Esakia space*](https://en.wikipedia.org/wiki/Esakia_space)
-/

open function

variables {F α β γ δ : Type*}

/-- The type of pseudo-epimorphisms, aka p-morphisms, aka bounded maps, from `α` to `β`. -/
structure pseudo_epimorphism (α β : Type*) [preorder α] [preorder β] extends α →o β :=
(exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : to_fun a ≤ b → ∃ c, a ≤ c ∧ to_fun c = b)

/-- The type of Esakia morphisms, aka continuous pseudo-epimorphisms, from `α` to `β`. -/
structure esakia_hom (α β : Type*) [topological_space α] [preorder α] [topological_space β]
  [preorder β] extends α →Co β :=
(exists_map_eq_of_map_le' ⦃a : α⦄ ⦃b : β⦄ : to_fun a ≤ b → ∃ c, a ≤ c ∧ to_fun c = b)

section
set_option old_structure_cmd true

/-- `pseudo_epimorphism_class F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `pseudo_epimorphism`. -/
class pseudo_epimorphism_class (F : Type*) (α β : out_param $ Type*) [preorder α] [preorder β]
  extends rel_hom_class F ((≤) : α → α → Prop) ((≤) : β → β → Prop) :=
(exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b)

/-- `esakia_hom_class F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `esakia_hom`. -/
class esakia_hom_class (F : Type*) (α β : out_param $ Type*) [topological_space α] [preorder α]
  [topological_space β] [preorder β]
  extends continuous_order_hom_class F α β :=
(exists_map_eq_of_map_le (f : F) ⦃a : α⦄ ⦃b : β⦄ : f a ≤ b → ∃ c, a ≤ c ∧ f c = b)

end

export pseudo_epimorphism_class (exists_map_eq_of_map_le)

@[priority 100] -- See note [lower instance priority]
instance pseudo_epimorphism_class.to_top_hom_class [partial_order α] [order_top α] [preorder β]
  [order_top β] [pseudo_epimorphism_class F α β] : top_hom_class F α β :=
{ map_top := λ f, let ⟨b, h⟩ := exists_map_eq_of_map_le f (@le_top _ _ _ $ f ⊤) in
                  by rw [←top_le_iff.1 h.1, h.2]
  .. ‹pseudo_epimorphism_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance order_iso_class.to_pseudo_epimorphism_class [preorder α] [preorder β]
  [order_iso_class F α β] : pseudo_epimorphism_class F α β :=
{ exists_map_eq_of_map_le :=
      λ f a b h, ⟨equiv_like.inv f b, (le_map_inv_iff f).2 h, equiv_like.right_inv _ _⟩,
  .. order_iso_class.to_order_hom_class }

@[priority 100] -- See note [lower instance priority]
instance esakia_hom_class.to_pseudo_epimorphism_class [topological_space α] [preorder α]
  [topological_space β] [preorder β] [esakia_hom_class F α β] : pseudo_epimorphism_class F α β :=
{ .. ‹esakia_hom_class F α β› }

instance [preorder α] [preorder β] [pseudo_epimorphism_class F α β] :
  has_coe_t F (pseudo_epimorphism α β) :=
⟨λ f, ⟨f, exists_map_eq_of_map_le f⟩⟩

instance [topological_space α] [preorder α] [topological_space β] [preorder β]
  [esakia_hom_class F α β] : has_coe_t F (esakia_hom α β) :=
⟨λ f, ⟨f, exists_map_eq_of_map_le f⟩⟩

/-! ### Pseudo-epimorphisms -/

namespace pseudo_epimorphism
variables [preorder α] [preorder β] [preorder γ] [preorder δ]

instance : pseudo_epimorphism_class (pseudo_epimorphism α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_rel := λ f, f.monotone',
  exists_map_eq_of_map_le := pseudo_epimorphism.exists_map_eq_of_map_le' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (pseudo_epimorphism α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : pseudo_epimorphism α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : pseudo_epimorphism α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `pseudo_epimorphism` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : pseudo_epimorphism α β) (f' : α → β) (h : f' = f) :
  pseudo_epimorphism α β :=
⟨f.to_order_hom.copy f' h, by simpa only [h.symm, to_fun_eq_coe] using f.exists_map_eq_of_map_le'⟩

@[simp] lemma coe_copy (f : pseudo_epimorphism α β) (f' : α → β) (h : f' = f) :
  ⇑(f.copy f' h) = f' :=
rfl

lemma copy_eq (f : pseudo_epimorphism α β) (f' : α → β) (h : f' = f) :
  f.copy f' h = f :=
fun_like.ext' h

variables (α)

/-- `id` as a `pseudo_epimorphism`. -/
protected def id : pseudo_epimorphism α α := ⟨order_hom.id, λ a b h, ⟨b, h, rfl⟩⟩

instance : inhabited (pseudo_epimorphism α α) := ⟨pseudo_epimorphism.id α⟩

@[simp] lemma coe_id : ⇑(pseudo_epimorphism.id α) = id := rfl
@[simp] lemma coe_id_order_hom : (pseudo_epimorphism.id α : α →o α) = order_hom.id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : pseudo_epimorphism.id α a = a := rfl

/-- Composition of `pseudo_epimorphism`s as a `pseudo_epimorphism`. -/
def comp (g : pseudo_epimorphism β γ) (f : pseudo_epimorphism α β) : pseudo_epimorphism α γ :=
⟨g.to_order_hom.comp f.to_order_hom, λ a b h₀, begin
  obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀,
  obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁,
  exact ⟨b, h₂, rfl⟩,
end⟩

@[simp] lemma coe_comp (g : pseudo_epimorphism β γ) (f : pseudo_epimorphism α β) :
  (g.comp f : α → γ) = g ∘ f := rfl
@[simp] lemma coe_comp_order_hom (g : pseudo_epimorphism β γ) (f : pseudo_epimorphism α β) :
  (g.comp f : α →o γ) = (g : β →o γ).comp f := rfl
@[simp] lemma comp_apply (g : pseudo_epimorphism β γ) (f : pseudo_epimorphism α β) (a : α) :
  (g.comp f) a = g (f a) := rfl
@[simp] lemma comp_assoc (h : pseudo_epimorphism γ δ) (g : pseudo_epimorphism β γ)
  (f : pseudo_epimorphism α β) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
@[simp] lemma comp_id (f : pseudo_epimorphism α β) : f.comp (pseudo_epimorphism.id α) = f :=
ext $ λ a, rfl
@[simp] lemma id_comp (f : pseudo_epimorphism α β) : (pseudo_epimorphism.id β).comp f = f :=
ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : pseudo_epimorphism β γ} {f : pseudo_epimorphism α β}
  (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : pseudo_epimorphism β γ} {f₁ f₂ : pseudo_epimorphism α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end pseudo_epimorphism

/-! ### Esakia morphisms -/

namespace esakia_hom
variables [topological_space α] [preorder α] [topological_space β] [preorder β]
  [topological_space γ] [preorder γ] [topological_space δ] [preorder δ]

/-- Reinterpret an `esakia_hom` as a `pseudo_epimorphism`. -/
def to_pseudo_epimorphism (f : esakia_hom α β) : pseudo_epimorphism α β := { ..f }

instance : esakia_hom_class (esakia_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h,
    by { obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f, obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g, congr' },
  map_rel := λ f, f.monotone',
  map_continuous := λ f, f.continuous_to_fun,
  exists_map_eq_of_map_le := λ f, f.exists_map_eq_of_map_le' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (esakia_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : esakia_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : esakia_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of an `esakia_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : esakia_hom α β) (f' : α → β) (h : f' = f) : esakia_hom α β :=
⟨f.to_continuous_order_hom.copy f' h,
  by simpa only [h.symm, to_fun_eq_coe] using f.exists_map_eq_of_map_le'⟩

@[simp] lemma coe_copy (f : esakia_hom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : esakia_hom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as an `esakia_hom`. -/
protected def id : esakia_hom α α := ⟨continuous_order_hom.id α, λ a b h, ⟨b, h, rfl⟩⟩

instance : inhabited (esakia_hom α α) := ⟨esakia_hom.id α⟩

@[simp] lemma coe_id : ⇑(esakia_hom.id α) = id := rfl
@[simp] lemma coe_id_continuous_order_hom :
  (esakia_hom.id α : α →Co α) = continuous_order_hom.id α := rfl
@[simp] lemma coe_id_pseudo_epimorphism :
  (esakia_hom.id α : pseudo_epimorphism α α) = pseudo_epimorphism.id α  := rfl

variables {α}

@[simp] lemma id_apply (a : α) : esakia_hom.id α a = a := rfl

/-- Composition of `esakia_hom`s as an `esakia_hom`. -/
def comp (g : esakia_hom β γ) (f : esakia_hom α β) : esakia_hom α γ :=
⟨g.to_continuous_order_hom.comp f.to_continuous_order_hom, λ a b h₀, begin
  obtain ⟨b, h₁, rfl⟩ := g.exists_map_eq_of_map_le' h₀,
  obtain ⟨b, h₂, rfl⟩ := f.exists_map_eq_of_map_le' h₁,
  exact ⟨b, h₂, rfl⟩,
end⟩

@[simp] lemma coe_comp (g : esakia_hom β γ) (f : esakia_hom α β) : (g.comp f : α → γ) = g ∘ f := rfl
@[simp] lemma comp_apply (g : esakia_hom β γ) (f : esakia_hom α β) (a : α) :
  (g.comp f) a = g (f a) := rfl
@[simp] lemma coe_comp_continuous_order_hom (g : esakia_hom β γ) (f : esakia_hom α β) :
  (g.comp f : α →Co γ) = (g : β →Co γ).comp f := rfl
@[simp] lemma coe_comp_pseudo_epimorphism (g : esakia_hom β γ) (f : esakia_hom α β) :
  (g.comp f : pseudo_epimorphism α γ) = (g : pseudo_epimorphism β γ).comp f := rfl
@[simp] lemma comp_assoc (h : esakia_hom γ δ) (g : esakia_hom β γ) (f : esakia_hom α β) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl
@[simp] lemma comp_id (f : esakia_hom α β) : f.comp (esakia_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : esakia_hom α β) : (esakia_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : esakia_hom β γ} {f : esakia_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : esakia_hom β γ} {f₁ f₂ : esakia_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end esakia_hom
