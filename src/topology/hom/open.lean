/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import topology.continuous_function.basic

/-!
# Continuous open maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled continuous open maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `continuous_open_map`: Continuous open maps.

## Typeclasses

* `continuous_open_map_class`
-/

open function

variables {F α β γ δ : Type*}

/-- The type of continuous open maps from `α` to `β`, aka Priestley homomorphisms. -/
structure continuous_open_map (α β : Type*) [topological_space α] [topological_space β]
  extends continuous_map α β :=
(map_open' : is_open_map to_fun)

infixr ` →CO `:25 := continuous_open_map

section
set_option old_structure_cmd true

/-- `continuous_open_map_class F α β` states that `F` is a type of continuous open maps.

You should extend this class when you extend `continuous_open_map`. -/
class continuous_open_map_class (F : Type*) (α β : out_param $ Type*) [topological_space α]
  [topological_space β] extends continuous_map_class F α β :=
(map_open (f : F) : is_open_map f)

end

export continuous_open_map_class (map_open)

instance [topological_space α] [topological_space β] [continuous_open_map_class F α β] :
  has_coe_t F (α →CO β) :=
⟨λ f, ⟨f, map_open f⟩⟩

/-! ### Continuous open maps -/

namespace continuous_open_map
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

instance : continuous_open_map_class (α →CO β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  map_open := λ f, f.map_open' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →CO β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : α →CO β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : α →CO β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `continuous_open_map` with a new `continuous_map` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →CO β) (f' : α → β) (h : f' = f) : α →CO β :=
⟨f.to_continuous_map.copy f' $ by exact h, h.symm.subst f.map_open'⟩

@[simp] lemma coe_copy (f : α →CO β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : α →CO β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `continuous_open_map`. -/
protected def id : α →CO α := ⟨continuous_map.id _, is_open_map.id⟩

instance : inhabited (α →CO α) := ⟨continuous_open_map.id _⟩

@[simp] lemma coe_id : ⇑(continuous_open_map.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : continuous_open_map.id α a = a := rfl

/-- Composition of `continuous_open_map`s as a `continuous_open_map`. -/
def comp (f : β →CO γ) (g : α →CO β) : continuous_open_map α γ :=
⟨f.to_continuous_map.comp g.to_continuous_map, f.map_open'.comp g.map_open'⟩

@[simp] lemma coe_comp (f : β →CO γ) (g : α →CO β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : β →CO γ) (g : α →CO β) (a : α) : (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : γ →CO δ) (g : β →CO γ) (h : α →CO β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : α →CO β) : f.comp (continuous_open_map.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : α →CO β) : (continuous_open_map.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : β →CO γ} {f : α →CO β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : β →CO γ} {f₁ f₂ : α →CO β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end continuous_open_map
