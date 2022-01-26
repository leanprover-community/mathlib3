/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.basic
import order.bounded_order

/-!
# Lattice homomorphisms

This file defines (bounded) lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `top_hom`: Maps which preserve `⊤`.
* `bot_hom`: Maps which preserve `⊥`.
* `sup_hom`: Maps which preserve `⊔`.
* `inf_hom`: Maps which preserve `⊓`.
* `lattice_hom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.
* `bounded_lattice_hom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `top_hom_class`
* `bot_hom_class`
* `sup_hom_class`
* `inf_hom_class`
* `lattice_hom_class`
* `bounded_lattice_hom_class`

## TODO

Do we need more intersections between `bot_hom`, `top_hom` and lattice homomorphisms?
-/

open function

variables {F α β γ δ : Type*}

/-- The type of `⊤`-preserving functions from `α` to `β`. -/
structure top_hom (α β : Type*) [has_top α] [has_top β] :=
(to_fun   : α → β)
(map_top' : to_fun ⊤ = ⊤)

/-- The type of `⊥`-preserving functions from `α` to `β`. -/
structure bot_hom (α β : Type*) [has_bot α] [has_bot β] :=
(to_fun   : α → β)
(map_bot' : to_fun ⊥ = ⊥)

/-- The type of `⊔`-preserving functions from `α` to `β`. -/
structure sup_hom (α β : Type*) [has_sup α] [has_sup β] :=
(to_fun   : α → β)
(map_sup' (a b : α) : to_fun (a ⊔ b) = to_fun a ⊔ to_fun b)

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
structure inf_hom (α β : Type*) [has_inf α] [has_inf β] :=
(to_fun   : α → β)
(map_inf' (a b : α) : to_fun (a ⊓ b) = to_fun a ⊓ to_fun b)

/-- The type of lattice homomorphisms from `α` to `β`. -/
structure lattice_hom (α β : Type*) [lattice α] [lattice β] extends sup_hom α β :=
(map_inf' (a b : α) : to_fun (a ⊓ b) = to_fun a ⊓ to_fun b)

/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
structure bounded_lattice_hom (α β : Type*) [lattice α] [lattice β] [bounded_order α]
  [bounded_order β]
  extends lattice_hom α β :=
(map_top' : to_fun ⊤ = ⊤)
(map_bot' : to_fun ⊥ = ⊥)

/-- `top_hom_class F α β` states that `F` is a type of `⊤`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class top_hom_class (F : Type*) (α β : out_param $ Type*) [has_top α] [has_top β]
  extends fun_like F α (λ _, β) :=
(map_top (f : F) : f ⊤ = ⊤)

/-- `bot_hom_class F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class bot_hom_class (F : Type*) (α β : out_param $ Type*) [has_bot α] [has_bot β]
  extends fun_like F α (λ _, β) :=
(map_bot (f : F) : f ⊥ = ⊥)

/-- `sup_hom_class F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class sup_hom_class (F : Type*) (α β : out_param $ Type*) [has_sup α] [has_sup β]
  extends fun_like F α (λ _, β) :=
(map_sup (f : F) (a b : α) : f (a ⊔ b) = f a ⊔ f b)

/-- `inf_hom_class F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `inf_hom`. -/
class inf_hom_class (F : Type*) (α β : out_param $ Type*) [has_inf α] [has_inf β]
  extends fun_like F α (λ _, β) :=
(map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b)

/-- `lattice_hom_class F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `sup_hom`. -/
class lattice_hom_class (F : Type*) (α β : out_param $ Type*) [lattice α] [lattice β]
  extends sup_hom_class F α β :=
(map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b)

/-- `bounded_lattice_hom_class F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `bounded_lattice_hom`. -/
class bounded_lattice_hom_class (F : Type*) (α β : out_param $ Type*) [lattice α] [lattice β]
  [bounded_order α] [bounded_order β]
  extends lattice_hom_class F α β :=
(map_top (f : F) : f ⊤ = ⊤)
(map_bot (f : F) : f ⊥ = ⊥)

export top_hom_class (map_top)
export bot_hom_class (map_bot)
export sup_hom_class (map_sup)
export inf_hom_class (map_inf)

attribute [simp] map_top map_bot map_sup map_inf

@[priority 100] -- See note [lower instance priority]
instance sup_hom_class.to_order_hom_class [semilattice_sup α] [semilattice_sup β]
  [sup_hom_class F α β] :
  order_hom_class F α β :=
⟨λ f a b h, by rw [←sup_eq_right, ←map_sup, sup_eq_right.2 h]⟩

@[priority 100] -- See note [lower instance priority]
instance inf_hom_class.to_order_hom_class [semilattice_inf α] [semilattice_inf β]
  [inf_hom_class F α β] : order_hom_class F α β :=
⟨λ f a b h, by rw [←inf_eq_left, ←map_inf, inf_eq_left.2 h]⟩

@[priority 100] -- See note [lower instance priority]
instance lattice_hom_class.to_inf_hom_class [lattice α] [lattice β] [lattice_hom_class F α β] :
  inf_hom_class F α β :=
{ .. ‹lattice_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance bounded_lattice_hom_class.to_top_hom_class [lattice α] [lattice β]
  [bounded_order α] [bounded_order β] [bounded_lattice_hom_class F α β] :
  top_hom_class F α β :=
{ .. ‹bounded_lattice_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance bounded_lattice_hom_class.to_bot_hom_class [lattice α] [lattice β]
  [bounded_order α] [bounded_order β] [bounded_lattice_hom_class F α β] :
  bot_hom_class F α β :=
{ .. ‹bounded_lattice_hom_class F α β› }

instance [has_top α] [has_top β] [top_hom_class F α β] : has_coe_t F (top_hom α β) :=
⟨λ f, ⟨f, map_top f⟩⟩

instance [has_bot α] [has_bot β] [bot_hom_class F α β] : has_coe_t F (bot_hom α β) :=
⟨λ f, ⟨f, map_bot f⟩⟩

instance [has_sup α] [has_sup β] [sup_hom_class F α β] : has_coe_t F (sup_hom α β) :=
⟨λ f, ⟨f, map_sup f⟩⟩

instance [has_inf α] [has_inf β] [inf_hom_class F α β] : has_coe_t F (inf_hom α β) :=
⟨λ f, ⟨f, map_inf f⟩⟩

instance [lattice α] [lattice β] [lattice_hom_class F α β] : has_coe_t F (lattice_hom α β) :=
⟨λ f, { to_fun := f, map_sup' := map_sup f, map_inf' := map_inf f }⟩

instance [lattice α] [lattice β] [bounded_order α] [bounded_order β]
  [bounded_lattice_hom_class F α β] : has_coe_t F (bounded_lattice_hom α β) :=
⟨λ f, { to_fun := f, map_top' := map_top f, map_bot' := map_bot f, ..(f : lattice_hom α β) }⟩

/-! ### Top homomorphisms -/

namespace top_hom
variables [has_top α]

section has_top
variables [has_top β] [has_top γ] [has_top δ]

instance : top_hom_class (top_hom α β) α β :=
{ coe := top_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_top := top_hom.map_top' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (top_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : top_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : top_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : top_hom α β) (f' : α → β) (h : f' = f) : top_hom α β :=
{ to_fun := f',
  map_top' := h.symm ▸ f.map_top' }

instance : inhabited (top_hom α β) := ⟨⟨λ _, ⊤, rfl⟩⟩

variables (α)

/-- `id` as a `top_hom`. -/
protected def id : top_hom α α := ⟨id, rfl⟩

@[simp] lemma coe_id : ⇑(top_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : top_hom.id α a = a := rfl

/-- Composition of `top_hom`s as a `top_hom`. -/
def comp (f : top_hom β γ) (g : top_hom α β) : top_hom α γ :=
{ to_fun := f ∘ g,
  map_top' := by rw [comp_apply, map_top, map_top] }

@[simp] lemma coe_comp (f : top_hom β γ) (g : top_hom α β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : top_hom β γ) (g : top_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : top_hom γ δ) (g : top_hom β γ) (h : top_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : top_hom α β) : f.comp (top_hom.id α) = f := top_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : top_hom α β) : (top_hom.id β).comp f = f := top_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : top_hom β γ} {f : top_hom α β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, top_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : top_hom β γ} {f₁ f₂ : top_hom α β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, top_hom.ext $ λ a, hg $
  by rw [←top_hom.comp_apply, h, top_hom.comp_apply], congr_arg _⟩

end has_top

instance [preorder β] [has_top β] : preorder (top_hom α β) :=
preorder.lift (coe_fn : top_hom α β → α → β)

instance [partial_order β] [has_top β] : partial_order (top_hom α β) :=
partial_order.lift _ fun_like.coe_injective

section order_top
variables [preorder β] [order_top β]

instance : order_top (top_hom α β) := ⟨⟨⊤, rfl⟩, λ _, le_top⟩

@[simp] lemma coe_top : ⇑(⊤ : top_hom α β) = ⊤ := rfl
@[simp] lemma top_apply (a : α) : (⊤ : top_hom α β) a = ⊤ := rfl

end order_top

section semilattice_inf
variables [semilattice_inf β] [order_top β] (f g : top_hom α β)

instance : has_inf (top_hom α β) :=
⟨λ f g, ⟨f ⊓ g, by rw [pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

instance : semilattice_inf (top_hom α β) := fun_like.coe_injective.semilattice_inf _ $ λ _ _, rfl

@[simp] lemma coe_inf : ⇑(f ⊓ g) = f ⊓ g := rfl
@[simp] lemma inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

end semilattice_inf

section semilattice_sup
variables [semilattice_sup β] [order_top β] (f g : top_hom α β)

instance : has_sup (top_hom α β) :=
⟨λ f g, ⟨f ⊔ g, by rw [pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

instance : semilattice_sup (top_hom α β) := fun_like.coe_injective.semilattice_sup _ $ λ _ _, rfl

@[simp] lemma coe_sup : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

end semilattice_sup

instance [lattice β] [order_top β] : lattice (top_hom α β) :=
fun_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance [distrib_lattice β] [order_top β] : distrib_lattice (top_hom α β) :=
fun_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

end top_hom

/-! ### Bot homomorphisms -/

namespace bot_hom
variables [has_bot α]

section has_bot
variables [has_bot β] [has_bot γ] [has_bot δ]

instance : bot_hom_class (bot_hom α β) α β :=
{ coe := bot_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_bot := bot_hom.map_bot' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (bot_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : bot_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : bot_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : bot_hom α β) (f' : α → β) (h : f' = f) : bot_hom α β :=
{ to_fun := f',
  map_bot' := h.symm ▸ f.map_bot' }

instance : inhabited (bot_hom α β) := ⟨⟨λ _, ⊥, rfl⟩⟩

variables (α)

/-- `id` as a `bot_hom`. -/
protected def id : bot_hom α α := ⟨id, rfl⟩

@[simp] lemma coe_id : ⇑(bot_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : bot_hom.id α a = a := rfl

/-- Composition of `bot_hom`s as a `bot_hom`. -/
def comp (f : bot_hom β γ) (g : bot_hom α β) : bot_hom α γ :=
{ to_fun := f ∘ g,
  map_bot' := by rw [comp_apply, map_bot, map_bot] }

@[simp] lemma coe_comp (f : bot_hom β γ) (g : bot_hom α β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : bot_hom β γ) (g : bot_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : bot_hom γ δ) (g : bot_hom β γ) (h : bot_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : bot_hom α β) : f.comp (bot_hom.id α) = f := bot_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : bot_hom α β) : (bot_hom.id β).comp f = f := bot_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : bot_hom β γ} {f : bot_hom α β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, bot_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : bot_hom β γ} {f₁ f₂ : bot_hom α β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, bot_hom.ext $ λ a, hg $
  by rw [←bot_hom.comp_apply, h, bot_hom.comp_apply], congr_arg _⟩

end has_bot

instance [preorder β] [has_bot β] : preorder (bot_hom α β) :=
preorder.lift (coe_fn : bot_hom α β → α → β)

instance [partial_order β] [has_bot β] : partial_order (bot_hom α β) :=
partial_order.lift _ fun_like.coe_injective

section order_bot
variables [preorder β] [order_bot β]

instance : order_bot (bot_hom α β) := ⟨⟨⊥, rfl⟩, λ _, bot_le⟩

@[simp] lemma coe_bot : ⇑(⊥ : bot_hom α β) = ⊥ := rfl
@[simp] lemma bot_apply (a : α) : (⊥ : bot_hom α β) a = ⊥ := rfl

end order_bot

section semilattice_inf
variables [semilattice_inf β] [order_bot β] (f g : bot_hom α β)

instance : has_inf (bot_hom α β) :=
⟨λ f g, ⟨f ⊓ g, by rw [pi.inf_apply, map_bot, map_bot, inf_bot_eq]⟩⟩

instance : semilattice_inf (bot_hom α β) := fun_like.coe_injective.semilattice_inf _ $ λ _ _, rfl

@[simp] lemma coe_inf : ⇑(f ⊓ g) = f ⊓ g := rfl
@[simp] lemma inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

end semilattice_inf

section semilattice_sup
variables [semilattice_sup β] [order_bot β] (f g : bot_hom α β)

instance : has_sup (bot_hom α β) :=
⟨λ f g, ⟨f ⊔ g, by rw [pi.sup_apply, map_bot, map_bot, sup_bot_eq]⟩⟩

instance : semilattice_sup (bot_hom α β) := fun_like.coe_injective.semilattice_sup _ $ λ _ _, rfl

@[simp] lemma coe_sup : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

end semilattice_sup

instance [lattice β] [order_bot β] : lattice (bot_hom α β) :=
fun_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance [distrib_lattice β] [order_bot β] : distrib_lattice (bot_hom α β) :=
fun_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

end bot_hom

/-! ### Supremum homomorphisms -/

namespace sup_hom
variables [has_sup α]

section has_sup
variables [has_sup β] [has_sup γ] [has_sup δ]

instance : sup_hom_class (sup_hom α β) α β :=
{ coe := sup_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_sup := sup_hom.map_sup' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (sup_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : sup_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : sup_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sup_hom α β) (f' : α → β) (h : f' = f) : sup_hom α β :=
{ to_fun := f',
  map_sup' := h.symm ▸ f.map_sup' }

variables (α)

/-- `id` as a `sup_hom`. -/
protected def id : sup_hom α α := ⟨id, λ a b, rfl⟩

instance : inhabited (sup_hom α α) := ⟨sup_hom.id α⟩

@[simp] lemma coe_id : ⇑(sup_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : sup_hom.id α a = a := rfl

/-- Composition of `sup_hom`s as a `sup_hom`. -/
def comp (f : sup_hom β γ) (g : sup_hom α β) : sup_hom α γ :=
{ to_fun := f ∘ g,
  map_sup' := λ a b, by rw [comp_apply, map_sup, map_sup] }

@[simp] lemma coe_comp (f : sup_hom β γ) (g : sup_hom α β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : sup_hom β γ) (g : sup_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : sup_hom γ δ) (g : sup_hom β γ) (h : sup_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : sup_hom α β) : f.comp (sup_hom.id α) = f := sup_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : sup_hom α β) : (sup_hom.id β).comp f = f := sup_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : sup_hom β γ} {f : sup_hom α β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, sup_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : sup_hom β γ} {f₁ f₂ : sup_hom α β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, sup_hom.ext $ λ a, hg $
  by rw [←sup_hom.comp_apply, h, sup_hom.comp_apply], congr_arg _⟩

end has_sup

variables [semilattice_sup β]

instance : has_sup (sup_hom α β) :=
⟨λ f g, ⟨f ⊔ g, λ a b, by { rw [pi.sup_apply, map_sup, map_sup], exact sup_sup_sup_comm _ _ _ _ }⟩⟩

instance : semilattice_sup (sup_hom α β) := fun_like.coe_injective.semilattice_sup _ $ λ f g, rfl

@[simp] lemma coe_sup (f g : sup_hom α β) : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma sup_apply (f g : sup_hom α β) (a : α): (f ⊔ g) a = f a ⊔ g a := rfl

variables (α)

/-- The constant function as a `sup_hom`. -/
def const (b : β) : sup_hom α β := ⟨λ _, b, λ _ _, sup_idem.symm⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

end sup_hom

/-! ### Infimum homomorphisms -/

namespace inf_hom
variables [has_inf α]

section has_inf
variables [has_inf β] [has_inf γ] [has_inf δ]

instance : inf_hom_class (inf_hom α β) α β :=
{ coe := inf_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_inf := inf_hom.map_inf' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (inf_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : inf_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : inf_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : inf_hom α β) (f' : α → β) (h : f' = f) : inf_hom α β :=
{ to_fun := f',
  map_inf' := h.symm ▸ f.map_inf' }

variables (α)

/-- `id` as an `inf_hom`. -/
protected def id : inf_hom α α := ⟨id, λ a b, rfl⟩

instance : inhabited (inf_hom α α) := ⟨inf_hom.id α⟩

@[simp] lemma coe_id : ⇑(inf_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : inf_hom.id α a = a := rfl

/-- Composition of `inf_hom`s as a `inf_hom`. -/
def comp (f : inf_hom β γ) (g : inf_hom α β) : inf_hom α γ :=
{ to_fun := f ∘ g,
  map_inf' := λ a b, by rw [comp_apply, map_inf, map_inf] }

@[simp] lemma coe_comp (f : inf_hom β γ) (g : inf_hom α β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : inf_hom β γ) (g : inf_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : inf_hom γ δ) (g : inf_hom β γ) (h : inf_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : inf_hom α β) : f.comp (inf_hom.id α) = f := inf_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : inf_hom α β) : (inf_hom.id β).comp f = f := inf_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : inf_hom β γ} {f : inf_hom α β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, inf_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : inf_hom β γ} {f₁ f₂ : inf_hom α β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, inf_hom.ext $ λ a, hg $
  by rw [←inf_hom.comp_apply, h, inf_hom.comp_apply], congr_arg _⟩

end has_inf

variables [semilattice_inf β]

instance : has_inf (inf_hom α β) :=
⟨λ f g, ⟨f ⊓ g, λ a b, by { rw [pi.inf_apply, map_inf, map_inf], exact inf_inf_inf_comm _ _ _ _ }⟩⟩

instance : semilattice_inf (inf_hom α β) := fun_like.coe_injective.semilattice_inf _ $ λ f g, rfl

@[simp] lemma coe_inf (f g : inf_hom α β) : ⇑(f ⊓ g) = f ⊓ g := rfl
@[simp] lemma inf_apply (f g : inf_hom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

variables (α)

/-- The constant function as an `inf_hom`. -/
def const (b : β) : inf_hom α β := ⟨λ _, b, λ _ _, inf_idem.symm⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

end inf_hom

/-! ### Lattice homomorphisms -/

namespace lattice_hom
variables [lattice α] [lattice β] [lattice γ] [lattice δ]

/-- Reinterpret a `lattice_hom` as an `inf_hom`. -/
def to_inf_hom (f : lattice_hom α β) : inf_hom α β := { ..f }

instance : lattice_hom_class (lattice_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr',
  map_sup := λ f, f.map_sup',
  map_inf := λ f, f.map_inf' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (lattice_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : lattice_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : lattice_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `lattice_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : lattice_hom α β) (f' : α → β) (h : f' = f) : lattice_hom α β :=
{ to_fun := f',
  .. f.to_sup_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_inf_hom.copy f' $ by { ext, exact congr_fun h _ } }

variables (α)

/-- `id` as a `lattice_hom`. -/
protected def id : lattice_hom α α :=
{ to_fun := id,
  map_sup' := λ _ _, rfl,
  map_inf' := λ _ _, rfl }

instance : inhabited (lattice_hom α α) := ⟨lattice_hom.id α⟩

@[simp] lemma coe_id : ⇑(lattice_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : lattice_hom.id α a = a := rfl

/-- Composition of `lattice_hom`s as a `lattice_hom`. -/
def comp (f : lattice_hom β γ) (g : lattice_hom α β) : lattice_hom α γ :=
{ ..f.to_sup_hom.comp g.to_sup_hom, ..f.to_inf_hom.comp g.to_inf_hom }

@[simp] lemma coe_comp (f : lattice_hom β γ) (g : lattice_hom α β) : (f.comp g : α → γ) = f ∘ g :=
rfl
@[simp] lemma comp_apply (f : lattice_hom β γ) (g : lattice_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma coe_comp_sup_hom (f : lattice_hom β γ) (g : lattice_hom α β) :
  (f.comp g : sup_hom α γ) = (f : sup_hom β γ).comp g := rfl
@[simp] lemma coe_comp_inf_hom (f : lattice_hom β γ) (g : lattice_hom α β) :
  (f.comp g : inf_hom α γ) = (f : inf_hom β γ).comp g := rfl
@[simp] lemma comp_assoc (f : lattice_hom γ δ) (g : lattice_hom β γ) (h : lattice_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : lattice_hom α β) : f.comp (lattice_hom.id α) = f :=
lattice_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : lattice_hom α β) : (lattice_hom.id β).comp f = f :=
lattice_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : lattice_hom β γ} {f : lattice_hom α β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, lattice_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : lattice_hom β γ} {f₁ f₂ : lattice_hom α β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, lattice_hom.ext $ λ a, hg $
  by rw [←lattice_hom.comp_apply, h, lattice_hom.comp_apply], congr_arg _⟩

end lattice_hom

namespace order_hom
variables [linear_order α] [lattice β]

/-- Reinterpret an `order_hom` to a linear order as a `lattice_hom`. -/
def to_lattice_hom (f : α →o β) : lattice_hom α β :=
{ to_fun := f,
  map_sup' := λ a b, begin
    obtain h | h := le_total a b,
    { rw [sup_eq_right.2 h, sup_eq_right.2 (f.mono h)] },
    { rw [sup_eq_left.2 h, sup_eq_left.2 (f.mono h)] }
  end,
  map_inf' := λ a b, begin
    obtain h | h := le_total a b,
    { rw [inf_eq_left.2 h, inf_eq_left.2 (f.mono h)] },
    { rw [inf_eq_right.2 h, inf_eq_right.2 (f.mono h)] }
  end }

end order_hom

/-! ### Bounded lattice homomorphisms -/

namespace bounded_lattice_hom
variables [lattice α] [lattice β] [lattice γ] [lattice δ] [bounded_order α] [bounded_order β]
  [bounded_order γ] [bounded_order δ]

/-- Reinterpret a `bounded_lattice_hom` as a `top_hom`. -/
def to_top_hom (f : bounded_lattice_hom α β) : top_hom α β := { ..f }

/-- Reinterpret a `bounded_lattice_hom` as a `bot_hom`. -/
def to_bot_hom (f : bounded_lattice_hom α β) : bot_hom α β := { ..f }

instance : bounded_lattice_hom_class (bounded_lattice_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr',
  map_sup := λ f, f.map_sup',
  map_inf := λ f, f.map_inf',
  map_top := λ f, f.map_top',
  map_bot := λ f, f.map_bot' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (bounded_lattice_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : bounded_lattice_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : bounded_lattice_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bounded_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : bounded_lattice_hom α β) (f' : α → β) (h : f' = f) :
  bounded_lattice_hom α β :=
{ to_fun := f',
  .. f.to_lattice_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_top_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_bot_hom.copy f' $ by { ext, exact congr_fun h _ } }

variables (α)

/-- `id` as a `bounded_lattice_hom`. -/
protected def id : bounded_lattice_hom α α :=
{ to_fun := id,
  map_sup' := λ _ _, rfl,
  map_inf' := λ _ _, rfl,
  map_top' := rfl,
  map_bot' := rfl }

instance : inhabited (bounded_lattice_hom α α) := ⟨bounded_lattice_hom.id α⟩

@[simp] lemma coe_id : ⇑(bounded_lattice_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : bounded_lattice_hom.id α a = a := rfl

/-- Composition of `bounded_lattice_hom`s as a `bounded_lattice_hom`. -/
def comp (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) : bounded_lattice_hom α γ :=
{ ..f.to_lattice_hom.comp g.to_lattice_hom,
  ..f.to_top_hom.comp g.to_top_hom, ..f.to_bot_hom.comp g.to_bot_hom }

@[simp] lemma coe_comp (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) :
  (f.comp g : α → γ) = f ∘ g :=
rfl
@[simp] lemma comp_apply (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma coe_comp_lattice_hom (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) :
  (f.comp g : lattice_hom α γ) = (f : lattice_hom β γ).comp g := rfl
@[simp] lemma coe_comp_sup_hom (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) :
  (f.comp g : sup_hom α γ) = (f : sup_hom β γ).comp g := rfl
@[simp] lemma coe_comp_inf_hom (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) :
  (f.comp g : inf_hom α γ) = (f : inf_hom β γ).comp g := rfl
@[simp] lemma comp_assoc (f : bounded_lattice_hom γ δ) (g : bounded_lattice_hom β γ)
  (h : bounded_lattice_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : bounded_lattice_hom α β) : f.comp (bounded_lattice_hom.id α) = f :=
bounded_lattice_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : bounded_lattice_hom α β) : (bounded_lattice_hom.id β).comp f = f :=
bounded_lattice_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : bounded_lattice_hom β γ} {f : bounded_lattice_hom α β}
  (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, bounded_lattice_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : bounded_lattice_hom β γ} {f₁ f₂ : bounded_lattice_hom α β}
  (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, bounded_lattice_hom.ext $ λ a, hg $
  by rw [←bounded_lattice_hom.comp_apply, h, bounded_lattice_hom.comp_apply], congr_arg _⟩

end bounded_lattice_hom
