/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import topology.bitopology.basic
import topology.continuous_function.basic

/-!
# Bicontinuous maps

This file defines bicontinuous maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `bicontinuous_map`: Bicontinuous maps. Maps which are continuous as functions between the first
  topologies and as functions between the seocnd topologies.

## Typeclasses

* `bicontinuous_map_class`

## Notation

* `α →CC β`: Bicontinuous maps from `α` to `β`
-/

open function

variables {F α β γ δ : Type*}

/-- The type of bicontinuous maps from `α` to `β`.

When you extend this structure, make sure to extend `bicontinuous_map_class`. -/
structure bicontinuous_map (α β : Type*) [bitopological_space α] [bitopological_space β] :=
(to_fun : α → β)
(continuous_fst' : continuous (to_top_fst ∘ to_fun ∘ of_top_fst) . tactic.interactive.continuity')
(continuous_snd' : continuous (to_top_snd ∘ to_fun ∘ of_top_snd) . tactic.interactive.continuity')

infix ` →CC `:25 := bicontinuous_map

/-- `bicontinuous_map_class F α β` states that `F` is a type of bicontinuous maps.

You should extend this class when you extend `bicontinuous_map`. -/
class bicontinuous_map_class (F : Type*) (α β : out_param $ Type*) [bitopological_space α]
  [bitopological_space β]
  extends fun_like F α (λ _, β) :=
(continuous_map_fst (f : F) : continuous (to_top_fst ∘ f ∘ of_top_fst))
(continuous_map_snd (f : F) : continuous (to_top_snd ∘ f ∘ of_top_snd))

export bicontinuous_map_class (continuous_map_fst continuous_map_snd)

instance [bitopological_space α] [bitopological_space β] [bicontinuous_map_class F α β] :
  has_coe_t F (α →CC β) :=
⟨λ f, ⟨f, continuous_map_fst f, continuous_map_snd f⟩⟩

instance continuous_map.bicontinuous_map_class [topological_space α] [topological_space β] :
  bicontinuous_map_class (C(α, β)) α β :=
{ coe := continuous_map.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  continuous_map_fst := continuous_map.continuous,
  continuous_map_snd := continuous_map.continuous }

/-! ### Bicontinuous maps -/

namespace bicontinuous_map
variables [bitopological_space α] [bitopological_space β] [bitopological_space γ]
  [bitopological_space δ]

instance : bicontinuous_map_class (α →CC β) α β :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  continuous_map_fst := λ f, f.continuous_fst',
  continuous_map_snd := λ f, f.continuous_snd' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →CC β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : α →CC β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : α →CC β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bicontinuous_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →CC β) (f' : α → β) (h : f' = f) : α →CC β :=
{ to_fun := f',
  continuous_fst' := h.symm ▸ f.continuous_fst',
  continuous_snd' := h.symm ▸ f.continuous_snd' }

variables (α)

/-- `id` as a `bicontinuous_map`. -/
protected def id : bicontinuous_map α α := ⟨id, continuous_id, continuous_id⟩

instance : inhabited (bicontinuous_map α α) := ⟨bicontinuous_map.id α⟩

@[simp] lemma coe_id : ⇑(bicontinuous_map.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : bicontinuous_map.id α a = a := rfl

/-- Composition of `bicontinuous_map`s as a `bicontinuous_map`. -/
def comp (f : β →CC γ) (g : α →CC β) : bicontinuous_map α γ :=
{ to_fun := f ∘ g,
  continuous_fst' := f.continuous_fst'.comp g.continuous_fst',
  continuous_snd' := f.continuous_snd'.comp g.continuous_snd' }

@[simp] lemma coe_comp (f : β →CC γ) (g : α →CC β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : β →CC γ) (g : α →CC β) (a : α) : (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : bicontinuous_map γ δ) (g : β →CC γ) (h : α →CC β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : α →CC β) : f.comp (bicontinuous_map.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : α →CC β) : (bicontinuous_map.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : β →CC γ} {f : α →CC β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : β →CC γ} {f₁ f₂ : α →CC β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end bicontinuous_map
