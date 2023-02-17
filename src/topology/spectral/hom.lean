/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import topology.continuous_function.basic

/-!
# Spectral maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines spectral maps. A map is spectral when it's continuous and the preimage of a
compact open set is compact open.

## Main declarations

* `is_spectral_map`: Predicate for a map to be spectral.
* `spectral_map`: Bundled spectral maps.
* `spectral_map_class`: Typeclass for a type to be a type of spectral maps.

## TODO

Once we have `spectral_space`, `is_spectral_map` should move to `topology.spectral.basic`.
-/

open function order_dual

variables {F α β γ δ : Type*}

section unbundled
variables [topological_space α] [topological_space β] [topological_space γ] {f : α → β} {s : set β}

/-- A function between topological spaces is spectral if it is continuous and the preimage of every
compact open set is compact open. -/
structure is_spectral_map (f : α → β) extends continuous f : Prop :=
(is_compact_preimage_of_is_open ⦃s : set β⦄ : is_open s → is_compact s → is_compact (f ⁻¹' s))

lemma is_compact.preimage_of_is_open (hf : is_spectral_map f) (h₀ : is_compact s) (h₁ : is_open s) :
  is_compact (f ⁻¹' s) :=
hf.is_compact_preimage_of_is_open h₁ h₀

lemma is_spectral_map.continuous {f : α → β} (hf : is_spectral_map f) : continuous f :=
hf.to_continuous

lemma is_spectral_map_id : is_spectral_map (@id α) := ⟨continuous_id, λ s _, id⟩

lemma is_spectral_map.comp {f : β → γ} {g : α → β} (hf : is_spectral_map f)
  (hg : is_spectral_map g) :
  is_spectral_map (f ∘ g) :=
⟨hf.continuous.comp hg.continuous,
  λ s hs₀ hs₁, (hs₁.preimage_of_is_open hf hs₀).preimage_of_is_open hg (hs₀.preimage hf.continuous)⟩

end unbundled

/-- The type of spectral maps from `α` to `β`. -/
structure spectral_map (α β : Type*) [topological_space α] [topological_space β] :=
(to_fun : α → β)
(spectral' : is_spectral_map to_fun)

section
set_option old_structure_cmd true

/-- `spectral_map_class F α β` states that `F` is a type of spectral maps.

You should extend this class when you extend `spectral_map`. -/
class spectral_map_class (F : Type*) (α β : out_param $ Type*) [topological_space α]
  [topological_space β]
  extends fun_like F α (λ _, β) :=
(map_spectral (f : F) : is_spectral_map f)

end

export spectral_map_class (map_spectral)

attribute [simp] map_spectral

@[priority 100] -- See note [lower instance priority]
instance spectral_map_class.to_continuous_map_class [topological_space α] [topological_space β]
  [spectral_map_class F α β] :
  continuous_map_class F α β :=
{ map_continuous := λ f, (map_spectral f).continuous,
  ..‹spectral_map_class F α β› }

instance [topological_space α] [topological_space β] [spectral_map_class F α β] :
  has_coe_t F (spectral_map α β) :=
⟨λ f, ⟨_, map_spectral f⟩⟩

/-! ### Spectral maps -/

namespace spectral_map
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

/-- Reinterpret a `spectral_map` as a `continuous_map`. -/
def to_continuous_map (f : spectral_map α β) : continuous_map α β := ⟨_, f.spectral'.continuous⟩

instance : spectral_map_class (spectral_map α β) α β :=
{ coe := spectral_map.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_spectral := λ f, f.spectral' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (spectral_map α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : spectral_map α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : spectral_map α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `spectral_map` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : spectral_map α β) (f' : α → β) (h : f' = f) : spectral_map α β :=
⟨f', h.symm.subst f.spectral'⟩

@[simp] lemma coe_copy (f : spectral_map α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : spectral_map α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `spectral_map`. -/
protected def id : spectral_map α α := ⟨id, is_spectral_map_id⟩

instance : inhabited (spectral_map α α) := ⟨spectral_map.id α⟩

@[simp] lemma coe_id : ⇑(spectral_map.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : spectral_map.id α a = a := rfl

/-- Composition of `spectral_map`s as a `spectral_map`. -/
def comp (f : spectral_map β γ) (g : spectral_map α β) : spectral_map α γ :=
⟨f.to_continuous_map.comp g.to_continuous_map, f.spectral'.comp g.spectral'⟩

@[simp] lemma coe_comp (f : spectral_map β γ) (g : spectral_map α β) : (f.comp g : α → γ) = f ∘ g :=
rfl
@[simp] lemma comp_apply (f : spectral_map β γ) (g : spectral_map α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma coe_comp_continuous_map (f : spectral_map β γ) (g : spectral_map α β) :
  (f.comp g : continuous_map α γ) = (f : continuous_map β γ).comp g := rfl
@[simp] lemma comp_assoc (f : spectral_map γ δ) (g : spectral_map β γ) (h : spectral_map α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : spectral_map α β) : f.comp (spectral_map.id α) = f :=
ext $ λ a, rfl
@[simp] lemma id_comp (f : spectral_map α β) : (spectral_map.id β).comp f = f :=
ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : spectral_map β γ} {f : spectral_map α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : spectral_map β γ} {f₁ f₂ : spectral_map α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end spectral_map
