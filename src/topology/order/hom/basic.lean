/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.basic
import topology.continuous_function.basic

/-!
# Continuous order homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines continuous order homomorphisms, that is maps which are both continuous and
monotone. They are also called Priestley homomorphisms because they are the morphisms of the
category of Priestley spaces.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `continuous_order_hom`: Continuous monotone functions, aka Priestley homomorphisms.

## Typeclasses

* `continuous_order_hom_class`
-/

open function

variables {F α β γ δ : Type*}

/-- The type of continuous monotone maps from `α` to `β`, aka Priestley homomorphisms. -/
structure continuous_order_hom (α β : Type*) [preorder α] [preorder β] [topological_space α]
  [topological_space β]
  extends order_hom α β :=
(continuous_to_fun : continuous to_fun)

infixr ` →Co `:25 := continuous_order_hom

section
set_option old_structure_cmd true

/-- `continuous_order_hom_class F α β` states that `F` is a type of continuous monotone maps.

You should extend this class when you extend `continuous_order_hom`. -/
class continuous_order_hom_class (F : Type*) (α β : out_param $ Type*) [preorder α] [preorder β]
  [topological_space α] [topological_space β]
  extends rel_hom_class F ((≤) : α → α → Prop) ((≤) : β → β → Prop) :=
(map_continuous (f : F) : continuous f)

end

@[priority 100] -- See note [lower instance priority]
instance continuous_order_hom_class.to_continuous_map_class [preorder α] [preorder β]
  [topological_space α] [topological_space β] [continuous_order_hom_class F α β] :
  continuous_map_class F α β :=
{ ..‹continuous_order_hom_class F α β› }

instance [preorder α] [preorder β] [topological_space α] [topological_space β]
  [continuous_order_hom_class F α β] :
  has_coe_t F (α →Co β) :=
⟨λ f, { to_fun := f, monotone' := order_hom_class.mono f, continuous_to_fun := map_continuous f }⟩

/-! ### Top homomorphisms -/

namespace continuous_order_hom
variables [topological_space α] [preorder α] [topological_space β]

section preorder
variables [preorder β] [topological_space γ] [preorder γ] [topological_space δ] [preorder δ]

/-- Reinterpret a `continuous_order_hom` as a `continuous_map`. -/
def to_continuous_map (f : α →Co β) : C(α, β) := { ..f }

instance : continuous_order_hom_class (α →Co β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_rel := λ f, f.monotone',
  map_continuous := λ f, f.continuous_to_fun }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →Co β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : α →Co β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : α →Co β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `continuous_order_hom` with a new `continuous_map` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →Co β) (f' : α → β) (h : f' = f) : α →Co β :=
⟨f.to_order_hom.copy f' $ by exact h, h.symm.subst f.continuous_to_fun⟩

@[simp] lemma coe_copy (f : α →Co β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : α →Co β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `continuous_order_hom`. -/
protected def id : α →Co α := ⟨order_hom.id, continuous_id⟩

instance : inhabited (α →Co α) := ⟨continuous_order_hom.id _⟩

@[simp] lemma coe_id : ⇑(continuous_order_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : continuous_order_hom.id α a = a := rfl

/-- Composition of `continuous_order_hom`s as a `continuous_order_hom`. -/
def comp (f : β →Co γ) (g : α →Co β) : continuous_order_hom α γ :=
⟨f.to_order_hom.comp g.to_order_hom, f.continuous_to_fun.comp g.continuous_to_fun⟩

@[simp] lemma coe_comp (f : β →Co γ) (g : α →Co β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : β →Co γ) (g : α →Co β) (a : α) : (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : γ →Co δ) (g : β →Co γ) (h : α →Co β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : α →Co β) : f.comp (continuous_order_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : α →Co β) : (continuous_order_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : β →Co γ} {f : α →Co β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : β →Co γ} {f₁ f₂ : α →Co β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

instance : preorder (α →Co β) := preorder.lift (coe_fn : (α →Co β) → α → β)

end preorder

instance [partial_order β] : partial_order (α →Co β) := partial_order.lift _ fun_like.coe_injective

end continuous_order_hom
