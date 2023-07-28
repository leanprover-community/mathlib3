/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import topology.bornology.basic

/-!
# Locally bounded maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines locally bounded maps between bornologies.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `locally_bounded_map`: Locally bounded maps. Maps which preserve boundedness.

## Typeclasses

* `locally_bounded_map_class`
-/

open bornology filter function set

variables {F α β γ δ : Type*}

/-- The type of bounded maps from `α` to `β`, the maps which send a bounded set to a bounded set. -/
structure locally_bounded_map (α β : Type*) [bornology α] [bornology β] :=
(to_fun : α → β)
(comap_cobounded_le' : (cobounded β).comap to_fun ≤ cobounded α)

section
set_option old_structure_cmd true

/-- `locally_bounded_map_class F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `locally_bounded_map`. -/
class locally_bounded_map_class (F : Type*) (α β : out_param $ Type*) [bornology α]
  [bornology β]
  extends fun_like F α (λ _, β) :=
(comap_cobounded_le (f : F) : (cobounded β).comap f ≤ cobounded α)

end

export locally_bounded_map_class (comap_cobounded_le)

lemma is_bounded.image [bornology α] [bornology β] [locally_bounded_map_class F α β] {f : F}
  {s : set α} (hs : is_bounded s) : is_bounded (f '' s) :=
comap_cobounded_le_iff.1 (comap_cobounded_le f) hs

instance [bornology α] [bornology β] [locally_bounded_map_class F α β] :
  has_coe_t F (locally_bounded_map α β) :=
⟨λ f, ⟨f, comap_cobounded_le f⟩⟩

namespace locally_bounded_map
variables [bornology α] [bornology β] [bornology γ]
  [bornology δ]

instance : locally_bounded_map_class (locally_bounded_map α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  comap_cobounded_le := λ f, f.comap_cobounded_le' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (locally_bounded_map α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : locally_bounded_map α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : locally_bounded_map α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `locally_bounded_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : locally_bounded_map α β) (f' : α → β) (h : f' = f) :
  locally_bounded_map α β :=
⟨f', h.symm ▸ f.comap_cobounded_le'⟩

@[simp] lemma coe_copy (f : locally_bounded_map α β) (f' : α → β) (h : f' = f) :
  ⇑(f.copy f' h) = f' :=
rfl

lemma copy_eq (f : locally_bounded_map α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
fun_like.ext' h

/-- Construct a `locally_bounded_map` from the fact that the function maps bounded sets to bounded
sets. -/
def of_map_bounded (f : α → β) (h) : locally_bounded_map α β := ⟨f, comap_cobounded_le_iff.2 h⟩

@[simp] lemma coe_of_map_bounded (f : α → β) {h} : ⇑(of_map_bounded f h) = f := rfl
@[simp] lemma of_map_bounded_apply (f : α → β) {h} (a : α) : of_map_bounded f h a = f a := rfl

variables (α)

/-- `id` as a `locally_bounded_map`. -/
protected def id : locally_bounded_map α α := ⟨id, comap_id.le⟩

instance : inhabited (locally_bounded_map α α) := ⟨locally_bounded_map.id α⟩

@[simp] lemma coe_id : ⇑(locally_bounded_map.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : locally_bounded_map.id α a = a := rfl

/-- Composition of `locally_bounded_map`s as a `locally_bounded_map`. -/
def comp (f : locally_bounded_map β γ) (g : locally_bounded_map α β) : locally_bounded_map α γ :=
{ to_fun := f ∘ g,
  comap_cobounded_le' :=
    comap_comap.ge.trans $ (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le' }

@[simp] lemma coe_comp (f : locally_bounded_map β γ) (g : locally_bounded_map α β) :
  ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : locally_bounded_map β γ) (g : locally_bounded_map α β) (a : α) :
  f.comp g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : locally_bounded_map γ δ) (g : locally_bounded_map β γ)
  (h : locally_bounded_map α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : locally_bounded_map α β) :
  f.comp (locally_bounded_map.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : locally_bounded_map α β) :
  (locally_bounded_map.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : locally_bounded_map β γ} {f : locally_bounded_map α β}
  (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : locally_bounded_map β γ} {f₁ f₂ : locally_bounded_map α β}
  (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end locally_bounded_map
