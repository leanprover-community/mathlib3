/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.filter.bornology

/-!
# Bounded maps

This file defines bounded maps between bornological spaces.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `bounded_map`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `bounded_map_class`
-/

open filter function

variables {F α β γ δ : Type*}

/-- The type of bounded maps from `α` to `β`, the maps which send a bounded set to a bounded set. -/
structure bounded_map (α β : Type*) [bornological_space α] [bornological_space β] :=
(to_fun : α → β)
(comap_cobounded_le' : cobounded.comap to_fun ≤ cobounded)

/-- `bounded_map_class F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `bounded_map`. -/
class bounded_map_class (F : Type*) (α β : out_param $ Type*) [bornological_space α]
  [bornological_space β]
  extends fun_like F α (λ _, β) :=
(comap_cobounded_le (f : F) : cobounded.comap f ≤ cobounded)

export bounded_map_class (comap_cobounded_le)

/-
TODO: Add instances from `continuous_linear_map_class` (warning, does not exist yet) to
`bounded_map_class` here, or alternately in the file with `continuous_linear_map_class`.
-/

instance [bornological_space α] [bornological_space β] [bounded_map_class F α β] :
  has_coe_t F (bounded_map α β) :=
⟨λ f, ⟨f, comap_cobounded_le f⟩⟩

namespace bounded_map
variables [bornological_space α] [bornological_space β] [bornological_space γ]
  [bornological_space δ]

instance : bounded_map_class (bounded_map α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  comap_cobounded_le := λ f, f.comap_cobounded_le' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (bounded_map α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : bounded_map α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : bounded_map α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bounded_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : bounded_map α β) (f' : α → β) (h : f' = f) : bounded_map α β :=
{ to_fun := f',
  comap_cobounded_le' := h.symm ▸ f.comap_cobounded_le' }

variables (α)

/-- `id` as a `bounded_map`. -/
protected def id : bounded_map α α := ⟨id, comap_id.le⟩

instance : inhabited (bounded_map α α) := ⟨bounded_map.id α⟩

@[simp] lemma coe_id : ⇑(bounded_map.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : bounded_map.id α a = a := rfl

/-- Composition of `bounded_map`s as a `bounded_map`. -/
def comp (f : bounded_map β γ) (g : bounded_map α β) : bounded_map α γ :=
{ to_fun := f ∘ g,
  comap_cobounded_le' :=
    comap_comap.ge.trans $ (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le' }

@[simp] lemma coe_comp (f : bounded_map β γ) (g : bounded_map α β) : (f.comp g : α → γ) = f ∘ g :=
rfl
@[simp] lemma comp_apply (f : bounded_map β γ) (g : bounded_map α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : bounded_map γ δ) (g : bounded_map β γ) (h : bounded_map α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : bounded_map α β) : f.comp (bounded_map.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : bounded_map α β) : (bounded_map.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : bounded_map β γ} {f : bounded_map α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : bounded_map β γ} {f₁ f₂ : bounded_map α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end bounded_map
