/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.complete_lattice
import order.hom.lattice

/-!
# Complete lattice homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines frame homorphisms and complete lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `Sup_hom`: Maps which preserve `⨆`.
* `Inf_hom`: Maps which preserve `⨅`.
* `frame_hom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `complete_lattice_hom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `Sup_hom_class`
* `Inf_hom_class`
* `frame_hom_class`
* `complete_lattice_hom_class`

## Concrete homs

* `complete_lattice.set_preimage`: `set.preimage` as a complete lattice homomorphism.

## TODO

Frame homs are Heyting homs.
-/

open function order_dual set

variables {F α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure Sup_hom (α β : Type*) [has_Sup α] [has_Sup β] :=
(to_fun   : α → β)
(map_Sup' (s : set α) : to_fun (Sup s) = Sup (to_fun '' s))

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure Inf_hom (α β : Type*) [has_Inf α] [has_Inf β] :=
(to_fun   : α → β)
(map_Inf' (s : set α) : to_fun (Inf s) = Inf (to_fun '' s))

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure frame_hom (α β : Type*) [complete_lattice α] [complete_lattice β]
  extends inf_top_hom α β :=
(map_Sup' (s : set α) : to_fun (Sup s) = Sup (to_fun '' s))

/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure complete_lattice_hom (α β : Type*) [complete_lattice α] [complete_lattice β]
  extends Inf_hom α β :=
(map_Sup' (s : set α) : to_fun (Sup s) = Sup (to_fun '' s))

section
set_option old_structure_cmd true

/-- `Sup_hom_class F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `Sup_hom`. -/
class Sup_hom_class (F : Type*) (α β : out_param $ Type*) [has_Sup α] [has_Sup β]
  extends fun_like F α (λ _, β) :=
(map_Sup (f : F) (s : set α) : f (Sup s) = Sup (f '' s))

/-- `Inf_hom_class F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `Inf_hom`. -/
class Inf_hom_class (F : Type*) (α β : out_param $ Type*) [has_Inf α] [has_Inf β]
  extends fun_like F α (λ _, β) :=
(map_Inf (f : F) (s : set α) : f (Inf s) = Inf (f '' s))

/-- `frame_hom_class F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `frame_hom`. -/
class frame_hom_class (F : Type*) (α β : out_param $ Type*) [complete_lattice α]
  [complete_lattice β] extends inf_top_hom_class F α β :=
(map_Sup (f : F) (s : set α) : f (Sup s) = Sup (f '' s))

/-- `complete_lattice_hom_class F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class complete_lattice_hom_class (F : Type*) (α β : out_param $ Type*) [complete_lattice α]
  [complete_lattice β] extends Inf_hom_class F α β :=
(map_Sup (f : F) (s : set α) : f (Sup s) = Sup (f '' s))

end

export Sup_hom_class (map_Sup)
export Inf_hom_class (map_Inf)

attribute [simp] map_Sup map_Inf

lemma map_supr [has_Sup α] [has_Sup β] [Sup_hom_class F α β] (f : F) (g : ι → α) :
  f (⨆ i, g i) = ⨆ i, f (g i) :=
by rw [supr, supr, map_Sup, set.range_comp]

lemma map_supr₂ [has_Sup α] [has_Sup β] [Sup_hom_class F α β] (f : F) (g : Π i, κ i → α) :
  f (⨆ i j, g i j) = ⨆ i j, f (g i j) :=
by simp_rw map_supr

lemma map_infi [has_Inf α] [has_Inf β] [Inf_hom_class F α β] (f : F) (g : ι → α) :
  f (⨅ i, g i) = ⨅ i, f (g i) :=
by rw [infi, infi, map_Inf, set.range_comp]

lemma map_infi₂ [has_Inf α] [has_Inf β] [Inf_hom_class F α β] (f : F) (g : Π i, κ i → α) :
  f (⨅ i j, g i j) = ⨅ i j, f (g i j) :=
by simp_rw map_infi

@[priority 100] -- See note [lower instance priority]
instance Sup_hom_class.to_sup_bot_hom_class [complete_lattice α] [complete_lattice β]
  [Sup_hom_class F α β] :
  sup_bot_hom_class F α β :=
{ map_sup := λ f a b, by rw [←Sup_pair, map_Sup, set.image_pair, Sup_pair],
  map_bot := λ f, by rw [←Sup_empty, map_Sup, set.image_empty, Sup_empty],
  ..‹Sup_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance Inf_hom_class.to_inf_top_hom_class [complete_lattice α] [complete_lattice β]
  [Inf_hom_class F α β] :
  inf_top_hom_class F α β :=
{ map_inf := λ f a b, by rw [←Inf_pair, map_Inf, set.image_pair, Inf_pair],
  map_top := λ f, by rw [←Inf_empty, map_Inf, set.image_empty, Inf_empty],
  ..‹Inf_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance frame_hom_class.to_Sup_hom_class [complete_lattice α] [complete_lattice β]
  [frame_hom_class F α β] :
  Sup_hom_class F α β :=
{ .. ‹frame_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance frame_hom_class.to_bounded_lattice_hom_class [complete_lattice α] [complete_lattice β]
  [frame_hom_class F α β] :
  bounded_lattice_hom_class F α β :=
{ .. ‹frame_hom_class F α β›, ..Sup_hom_class.to_sup_bot_hom_class }

@[priority 100] -- See note [lower instance priority]
instance complete_lattice_hom_class.to_frame_hom_class [complete_lattice α] [complete_lattice β]
  [complete_lattice_hom_class F α β] :
  frame_hom_class F α β :=
{ .. ‹complete_lattice_hom_class F α β›, ..Inf_hom_class.to_inf_top_hom_class }

@[priority 100] -- See note [lower instance priority]
instance complete_lattice_hom_class.to_bounded_lattice_hom_class [complete_lattice α]
  [complete_lattice β] [complete_lattice_hom_class F α β] :
  bounded_lattice_hom_class F α β :=
{ ..Sup_hom_class.to_sup_bot_hom_class, ..Inf_hom_class.to_inf_top_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso_class.to_Sup_hom_class [complete_lattice α] [complete_lattice β]
  [order_iso_class F α β] :
  Sup_hom_class F α β :=
{ map_Sup := λ f s, eq_of_forall_ge_iff $
                λ c, by simp only [←le_map_inv_iff, Sup_le_iff, set.ball_image_iff],
  .. show order_hom_class F α β, from infer_instance }

@[priority 100] -- See note [lower instance priority]
instance order_iso_class.to_Inf_hom_class [complete_lattice α] [complete_lattice β]
  [order_iso_class F α β] :
  Inf_hom_class F α β :=
{ map_Inf := λ f s, eq_of_forall_le_iff $
                λ c, by simp only [←map_inv_le_iff, le_Inf_iff, set.ball_image_iff],
  .. show order_hom_class F α β, from infer_instance }

@[priority 100] -- See note [lower instance priority]
instance order_iso_class.to_complete_lattice_hom_class [complete_lattice α] [complete_lattice β]
  [order_iso_class F α β] :
  complete_lattice_hom_class F α β :=
{ ..order_iso_class.to_Sup_hom_class,
  ..order_iso_class.to_lattice_hom_class,
  .. show Inf_hom_class F α β, from infer_instance }

instance [has_Sup α] [has_Sup β] [Sup_hom_class F α β] : has_coe_t F (Sup_hom α β) :=
⟨λ f, ⟨f, map_Sup f⟩⟩

instance [has_Inf α] [has_Inf β] [Inf_hom_class F α β] : has_coe_t F (Inf_hom α β) :=
⟨λ f, ⟨f, map_Inf f⟩⟩

instance [complete_lattice α] [complete_lattice β] [frame_hom_class F α β] :
  has_coe_t F (frame_hom α β) :=
⟨λ f, ⟨f, map_Sup f⟩⟩

instance [complete_lattice α] [complete_lattice β] [complete_lattice_hom_class F α β] :
  has_coe_t F (complete_lattice_hom α β) :=
⟨λ f, ⟨f, map_Sup f⟩⟩

/-! ### Supremum homomorphisms -/

namespace Sup_hom
variables [has_Sup α]

section has_Sup
variables [has_Sup β] [has_Sup γ] [has_Sup δ]

instance : Sup_hom_class (Sup_hom α β) α β :=
{ coe := Sup_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_Sup := Sup_hom.map_Sup' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (Sup_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : Sup_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : Sup_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `Sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : Sup_hom α β) (f' : α → β) (h : f' = f) : Sup_hom α β :=
{ to_fun := f',
  map_Sup' := h.symm ▸ f.map_Sup' }

@[simp] lemma coe_copy (f : Sup_hom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : Sup_hom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `Sup_hom`. -/
protected def id : Sup_hom α α := ⟨id, λ s, by rw [id, set.image_id]⟩

instance : inhabited (Sup_hom α α) := ⟨Sup_hom.id α⟩

@[simp] lemma coe_id : ⇑(Sup_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : Sup_hom.id α a = a := rfl

/-- Composition of `Sup_hom`s as a `Sup_hom`. -/
def comp (f : Sup_hom β γ) (g : Sup_hom α β) : Sup_hom α γ :=
{ to_fun := f ∘ g,
  map_Sup' := λ s, by rw [comp_apply, map_Sup, map_Sup, set.image_image] }

@[simp] lemma coe_comp (f : Sup_hom β γ) (g : Sup_hom α β) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : Sup_hom β γ) (g : Sup_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : Sup_hom γ δ) (g : Sup_hom β γ) (h : Sup_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : Sup_hom α β) : f.comp (Sup_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : Sup_hom α β) : (Sup_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : Sup_hom β γ} {f : Sup_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : Sup_hom β γ} {f₁ f₂ : Sup_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end has_Sup

variables [complete_lattice β]

instance : partial_order (Sup_hom α β) := partial_order.lift _ fun_like.coe_injective

instance : has_bot (Sup_hom α β) :=
⟨⟨λ _, ⊥, λ s, begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [set.image_empty, Sup_empty] },
  { rw [hs.image_const, Sup_singleton] }
end⟩⟩

instance : order_bot (Sup_hom α β) := ⟨⊥, λ f a, bot_le⟩

@[simp] lemma coe_bot : ⇑(⊥ : Sup_hom α β) = ⊥ := rfl
@[simp] lemma bot_apply (a : α) : (⊥ : Sup_hom α β) a = ⊥ := rfl

end Sup_hom

/-! ### Infimum homomorphisms -/

namespace Inf_hom
variables [has_Inf α]

section has_Inf
variables [has_Inf β] [has_Inf γ] [has_Inf δ]

instance : Inf_hom_class (Inf_hom α β) α β :=
{ coe := Inf_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_Inf := Inf_hom.map_Inf' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (Inf_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : Inf_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : Inf_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `Inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : Inf_hom α β) (f' : α → β) (h : f' = f) : Inf_hom α β :=
{ to_fun := f',
  map_Inf' := h.symm ▸ f.map_Inf' }

@[simp] lemma coe_copy (f : Inf_hom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : Inf_hom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as an `Inf_hom`. -/
protected def id : Inf_hom α α := ⟨id, λ s, by rw [id, set.image_id]⟩

instance : inhabited (Inf_hom α α) := ⟨Inf_hom.id α⟩

@[simp] lemma coe_id : ⇑(Inf_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : Inf_hom.id α a = a := rfl

/-- Composition of `Inf_hom`s as a `Inf_hom`. -/
def comp (f : Inf_hom β γ) (g : Inf_hom α β) : Inf_hom α γ :=
{ to_fun := f ∘ g,
  map_Inf' := λ s, by rw [comp_apply, map_Inf, map_Inf, set.image_image] }

@[simp] lemma coe_comp (f : Inf_hom β γ) (g : Inf_hom α β) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : Inf_hom β γ) (g : Inf_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : Inf_hom γ δ) (g : Inf_hom β γ) (h : Inf_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : Inf_hom α β) : f.comp (Inf_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : Inf_hom α β) : (Inf_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : Inf_hom β γ} {f : Inf_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : Inf_hom β γ} {f₁ f₂ : Inf_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end has_Inf

variables [complete_lattice β]

instance : partial_order (Inf_hom α β) := partial_order.lift _ fun_like.coe_injective

instance : has_top (Inf_hom α β) :=
⟨⟨λ _, ⊤, λ s, begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rw [set.image_empty, Inf_empty] },
  { rw [hs.image_const, Inf_singleton] }
end⟩⟩

instance : order_top (Inf_hom α β) := ⟨⊤, λ f a, le_top⟩

@[simp] lemma coe_top : ⇑(⊤ : Inf_hom α β) = ⊤ := rfl
@[simp] lemma top_apply (a : α) : (⊤ : Inf_hom α β) a = ⊤ := rfl

end Inf_hom

/-! ### Frame homomorphisms -/

namespace frame_hom
variables [complete_lattice α] [complete_lattice β] [complete_lattice γ] [complete_lattice δ]

instance : frame_hom_class (frame_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h,
    by { obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f, obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g, congr' },
  map_Sup := λ f, f.map_Sup',
  map_inf := λ f, f.map_inf',
  map_top := λ f, f.map_top' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (frame_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

/-- Reinterpret a `frame_hom` as a `lattice_hom`. -/
def to_lattice_hom (f : frame_hom α β) : lattice_hom α β := f

@[simp] lemma to_fun_eq_coe {f : frame_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : frame_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : frame_hom α β) (f' : α → β) (h : f' = f) : frame_hom α β :=
{ to_inf_top_hom := f.to_inf_top_hom.copy f' h, ..(f : Sup_hom α β).copy f' h }

@[simp] lemma coe_copy (f : frame_hom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : frame_hom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `frame_hom`. -/
protected def id : frame_hom α α := { to_inf_top_hom := inf_top_hom.id α, ..Sup_hom.id α }

instance : inhabited (frame_hom α α) := ⟨frame_hom.id α⟩

@[simp] lemma coe_id : ⇑(frame_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : frame_hom.id α a = a := rfl

/-- Composition of `frame_hom`s as a `frame_hom`. -/
def comp (f : frame_hom β γ) (g : frame_hom α β) : frame_hom α γ :=
{ to_inf_top_hom := f.to_inf_top_hom.comp g.to_inf_top_hom,
  ..(f : Sup_hom β γ).comp (g : Sup_hom α β) }

@[simp] lemma coe_comp (f : frame_hom β γ) (g : frame_hom α β) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : frame_hom β γ) (g : frame_hom α β) (a : α) : (f.comp g) a = f (g a) :=
rfl
@[simp] lemma comp_assoc (f : frame_hom γ δ) (g : frame_hom β γ) (h : frame_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : frame_hom α β) : f.comp (frame_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : frame_hom α β) : (frame_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : frame_hom β γ} {f : frame_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : frame_hom β γ} {f₁ f₂ : frame_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

instance : partial_order (frame_hom α β) := partial_order.lift _ fun_like.coe_injective

end frame_hom

/-! ### Complete lattice homomorphisms -/

namespace complete_lattice_hom
variables [complete_lattice α] [complete_lattice β] [complete_lattice γ] [complete_lattice δ]

instance : complete_lattice_hom_class (complete_lattice_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr',
  map_Sup := λ f, f.map_Sup',
  map_Inf := λ f, f.map_Inf' }

/-- Reinterpret a `complete_lattice_hom` as a `Sup_hom`. -/
def to_Sup_hom (f : complete_lattice_hom α β) : Sup_hom α β := f

/-- Reinterpret a `complete_lattice_hom` as a `bounded_lattice_hom`. -/
def to_bounded_lattice_hom (f : complete_lattice_hom α β) : bounded_lattice_hom α β := f

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (complete_lattice_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : complete_lattice_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : complete_lattice_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : complete_lattice_hom α β) (f' : α → β) (h : f' = f) :
  complete_lattice_hom α β :=
{ to_Inf_hom := f.to_Inf_hom.copy f' h, .. f.to_Sup_hom.copy f' h }

@[simp] lemma coe_copy (f : complete_lattice_hom α β) (f' : α → β) (h : f' = f) :
  ⇑(f.copy f' h) = f' :=
rfl

lemma copy_eq (f : complete_lattice_hom α β) (f' : α → β) (h : f' = f) :
  f.copy f' h = f :=
fun_like.ext' h

variables (α)

/-- `id` as a `complete_lattice_hom`. -/
protected def id : complete_lattice_hom α α := { to_fun := id, ..Sup_hom.id α, ..Inf_hom.id α }

instance : inhabited (complete_lattice_hom α α) := ⟨complete_lattice_hom.id α⟩

@[simp] lemma coe_id : ⇑(complete_lattice_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : complete_lattice_hom.id α a = a := rfl

/-- Composition of `complete_lattice_hom`s as a `complete_lattice_hom`. -/
def comp (f : complete_lattice_hom β γ) (g : complete_lattice_hom α β) : complete_lattice_hom α γ :=
{ to_Inf_hom := f.to_Inf_hom.comp g.to_Inf_hom, ..f.to_Sup_hom.comp g.to_Sup_hom }

@[simp] lemma coe_comp (f : complete_lattice_hom β γ) (g : complete_lattice_hom α β) :
  ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : complete_lattice_hom β γ) (g : complete_lattice_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : complete_lattice_hom γ δ) (g : complete_lattice_hom β γ)
  (h : complete_lattice_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : complete_lattice_hom α β) : f.comp (complete_lattice_hom.id α) = f :=
ext $ λ a, rfl
@[simp] lemma id_comp (f : complete_lattice_hom α β) : (complete_lattice_hom.id β).comp f = f :=
ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : complete_lattice_hom β γ} {f : complete_lattice_hom α β}
  (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : complete_lattice_hom β γ} {f₁ f₂ : complete_lattice_hom α β}
  (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end complete_lattice_hom

/-! ### Dual homs -/

namespace Sup_hom
variables [has_Sup α] [has_Sup β] [has_Sup γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps] protected def dual : Sup_hom α β ≃ Inf_hom αᵒᵈ βᵒᵈ :=
{ to_fun := λ f, ⟨to_dual ∘ f ∘ of_dual, f.map_Sup'⟩,
  inv_fun := λ f, ⟨of_dual ∘ f ∘ to_dual, f.map_Inf'⟩,
  left_inv := λ f, Sup_hom.ext $ λ a, rfl,
  right_inv := λ f, Inf_hom.ext $ λ a, rfl }

@[simp] lemma dual_id : (Sup_hom.id α).dual = Inf_hom.id _ := rfl
@[simp] lemma dual_comp (g : Sup_hom β γ) (f : Sup_hom α β) :
  (g.comp f).dual = g.dual.comp f.dual := rfl

@[simp] lemma symm_dual_id : Sup_hom.dual.symm (Inf_hom.id _) = Sup_hom.id α := rfl
@[simp] lemma symm_dual_comp (g : Inf_hom βᵒᵈ γᵒᵈ) (f : Inf_hom αᵒᵈ βᵒᵈ) :
  Sup_hom.dual.symm (g.comp f) = (Sup_hom.dual.symm g).comp (Sup_hom.dual.symm f) := rfl

end Sup_hom

namespace Inf_hom
variables [has_Inf α] [has_Inf β] [has_Inf γ]

/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps] protected def dual : Inf_hom α β ≃ Sup_hom αᵒᵈ βᵒᵈ :=
{ to_fun := λ f, { to_fun := to_dual ∘ f ∘ of_dual,
                   map_Sup' := λ _, congr_arg to_dual (map_Inf f _) },
  inv_fun := λ f, { to_fun := of_dual ∘ f ∘ to_dual,
                   map_Inf' := λ _, congr_arg of_dual (map_Sup f _) },
  left_inv := λ f, Inf_hom.ext $ λ a, rfl,
  right_inv := λ f, Sup_hom.ext $ λ a, rfl }

@[simp] lemma dual_id : (Inf_hom.id α).dual = Sup_hom.id _ := rfl
@[simp] lemma dual_comp (g : Inf_hom β γ) (f : Inf_hom α β) :
  (g.comp f).dual = g.dual.comp f.dual := rfl

@[simp] lemma symm_dual_id : Inf_hom.dual.symm (Sup_hom.id _) = Inf_hom.id α := rfl
@[simp] lemma symm_dual_comp (g : Sup_hom βᵒᵈ γᵒᵈ) (f : Sup_hom αᵒᵈ βᵒᵈ) :
  Inf_hom.dual.symm (g.comp f) = (Inf_hom.dual.symm g).comp (Inf_hom.dual.symm f) := rfl

end Inf_hom

namespace complete_lattice_hom
variables [complete_lattice α] [complete_lattice β] [complete_lattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps] protected def dual : complete_lattice_hom α β ≃ complete_lattice_hom αᵒᵈ βᵒᵈ :=
{ to_fun := λ f, ⟨f.to_Sup_hom.dual, f.map_Inf'⟩,
  inv_fun := λ f, ⟨f.to_Sup_hom.dual, f.map_Inf'⟩,
  left_inv := λ f, ext $ λ a, rfl,
  right_inv := λ f, ext $ λ a, rfl }

@[simp] lemma dual_id : (complete_lattice_hom.id α).dual = complete_lattice_hom.id _ := rfl
@[simp] lemma dual_comp (g : complete_lattice_hom β γ) (f : complete_lattice_hom α β) :
  (g.comp f).dual = g.dual.comp f.dual := rfl

@[simp] lemma symm_dual_id :
  complete_lattice_hom.dual.symm (complete_lattice_hom.id _) = complete_lattice_hom.id α := rfl
@[simp] lemma symm_dual_comp (g : complete_lattice_hom βᵒᵈ γᵒᵈ) (f : complete_lattice_hom αᵒᵈ βᵒᵈ) :
  complete_lattice_hom.dual.symm (g.comp f) =
    (complete_lattice_hom.dual.symm g).comp (complete_lattice_hom.dual.symm f) := rfl

end complete_lattice_hom

/-! ### Concrete homs -/

namespace complete_lattice_hom

/-- `set.preimage` as a complete lattice homomorphism.

See also `Sup_hom.set_image`. -/
def set_preimage (f : α → β) : complete_lattice_hom (set β) (set α) :=
{ to_fun := preimage f,
  map_Sup' := λ s, preimage_sUnion.trans $ by simp only [set.Sup_eq_sUnion, set.sUnion_image],
  map_Inf' := λ s, preimage_sInter.trans $ by simp only [set.Inf_eq_sInter, set.sInter_image] }

@[simp] lemma coe_set_preimage (f : α → β) : ⇑(set_preimage f) = preimage f := rfl
@[simp] lemma set_preimage_apply (f : α → β) (s : set β) : set_preimage f s = s.preimage f := rfl
@[simp] lemma set_preimage_id : set_preimage (id : α → α) = complete_lattice_hom.id _ := rfl
-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` synctatically)
lemma set_preimage_comp (g : β → γ) (f : α → β) :
  set_preimage (g ∘ f) = (set_preimage f).comp (set_preimage g) := rfl

end complete_lattice_hom

lemma set.image_Sup {f : α → β} (s : set (set α)) :
  f '' Sup s = Sup (image f '' s) :=
begin
  ext b,
  simp only [Sup_eq_sUnion, mem_image, mem_sUnion, exists_prop, sUnion_image, mem_Union],
  split,
  { rintros ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩, exact ⟨t, ht₁, a, ht₂, rfl⟩, },
  { rintros ⟨t, ht₁, a, ht₂, rfl⟩, exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩, },
end

/-- Using `set.image`, a function between types yields a `Sup_hom` between their lattices of
subsets.

See also `complete_lattice_hom.set_preimage`. -/
@[simps] def Sup_hom.set_image (f : α → β) : Sup_hom (set α) (set β) :=
{ to_fun := image f,
  map_Sup' := set.image_Sup }

/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps] def equiv.to_order_iso_set (e : α ≃ β) : set α ≃o set β :=
{ to_fun  := image e,
  inv_fun := image e.symm,
  left_inv  := λ s, by simp only [← image_comp, equiv.symm_comp_self, id.def, image_id'],
  right_inv := λ s, by simp only [← image_comp, equiv.self_comp_symm, id.def, image_id'],
  map_rel_iff' :=
    λ s t, ⟨λ h, by simpa using @monotone_image _ _ e.symm _ _ h, λ h, monotone_image h⟩ }

variables [complete_lattice α] (x : α × α)

/-- The map `(a, b) ↦ a ⊔ b` as a `Sup_hom`. -/
def sup_Sup_hom : Sup_hom (α × α) α :=
{ to_fun := λ x, x.1 ⊔ x.2,
  map_Sup' := λ s, by simp_rw [prod.fst_Sup, prod.snd_Sup, Sup_image, supr_sup_eq] }

/-- The map `(a, b) ↦ a ⊓ b` as an `Inf_hom`. -/
def inf_Inf_hom : Inf_hom (α × α) α :=
{ to_fun := λ x, x.1 ⊓ x.2,
  map_Inf' := λ s, by simp_rw [prod.fst_Inf, prod.snd_Inf, Inf_image, infi_inf_eq] }

@[simp, norm_cast] lemma sup_Sup_hom_apply : sup_Sup_hom x = x.1 ⊔ x.2 := rfl
@[simp, norm_cast] lemma inf_Inf_hom_apply : inf_Inf_hom x = x.1 ⊓ x.2 := rfl
