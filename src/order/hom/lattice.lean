/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice
import order.hom.bounded

/-!
# Lattice homomorphisms

This file defines (bounded) lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `sup_hom`: Maps which preserve `⊔`.
* `inf_hom`: Maps which preserve `⊓`.
* `sup_bot_hom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `inf_top_hom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `lattice_hom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.
* `bounded_lattice_hom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `sup_hom_class`
* `inf_hom_class`
* `sup_bot_hom_class`
* `inf_top_hom_class`
* `lattice_hom_class`
* `bounded_lattice_hom_class`

## TODO

Do we need more intersections between `bot_hom`, `top_hom` and lattice homomorphisms?
-/

open function order_dual

variables {F ι α β γ δ : Type*}

/-- The type of `⊔`-preserving functions from `α` to `β`. -/
structure sup_hom (α β : Type*) [has_sup α] [has_sup β] :=
(to_fun   : α → β)
(map_sup' (a b : α) : to_fun (a ⊔ b) = to_fun a ⊔ to_fun b)

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
structure inf_hom (α β : Type*) [has_inf α] [has_inf β] :=
(to_fun   : α → β)
(map_inf' (a b : α) : to_fun (a ⊓ b) = to_fun a ⊓ to_fun b)

/-- The type of finitary supremum-preserving homomorphisms from `α` to `β`. -/
structure sup_bot_hom (α β : Type*) [has_sup α] [has_sup β] [has_bot α] [has_bot β]
  extends sup_hom α β :=
(map_bot' : to_fun ⊥ = ⊥)

/-- The type of finitary infimum-preserving homomorphisms from `α` to `β`. -/
structure inf_top_hom (α β : Type*) [has_inf α] [has_inf β] [has_top α] [has_top β]
  extends inf_hom α β :=
(map_top' : to_fun ⊤ = ⊤)

/-- The type of lattice homomorphisms from `α` to `β`. -/
structure lattice_hom (α β : Type*) [lattice α] [lattice β] extends sup_hom α β :=
(map_inf' (a b : α) : to_fun (a ⊓ b) = to_fun a ⊓ to_fun b)

/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
structure bounded_lattice_hom (α β : Type*) [lattice α] [lattice β] [bounded_order α]
  [bounded_order β]
  extends lattice_hom α β :=
(map_top' : to_fun ⊤ = ⊤)
(map_bot' : to_fun ⊥ = ⊥)

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

/-- `sup_bot_hom_class F α β` states that `F` is a type of finitary supremum-preserving morphisms.

You should extend this class when you extend `sup_bot_hom`. -/
class sup_bot_hom_class (F : Type*) (α β : out_param $ Type*) [has_sup α] [has_sup β] [has_bot α]
  [has_bot β] extends sup_hom_class F α β :=
(map_bot (f : F) : f ⊥ = ⊥)

/-- `inf_top_hom_class F α β` states that `F` is a type of finitary infimum-preserving morphisms.

You should extend this class when you extend `sup_bot_hom`. -/
class inf_top_hom_class (F : Type*) (α β : out_param $ Type*) [has_inf α]
  [has_inf β] [has_top α] [has_top β] extends inf_hom_class F α β :=
(map_top (f : F) : f ⊤ = ⊤)

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
instance sup_bot_hom_class.to_bot_hom_class [has_sup α] [has_sup β] [has_bot α] [has_bot β]
  [sup_bot_hom_class F α β] :
  bot_hom_class F α β :=
{ .. ‹sup_bot_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance inf_top_hom_class.to_top_hom_class [has_inf α] [has_inf β] [has_top α] [has_top β]
  [inf_top_hom_class F α β] :
  top_hom_class F α β :=
{ .. ‹inf_top_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance lattice_hom_class.to_inf_hom_class [lattice α] [lattice β] [lattice_hom_class F α β] :
  inf_hom_class F α β :=
{ .. ‹lattice_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance bounded_lattice_hom_class.to_sup_bot_hom_class [lattice α] [lattice β]
  [bounded_order α] [bounded_order β] [bounded_lattice_hom_class F α β] :
  sup_bot_hom_class F α β :=
{ .. ‹bounded_lattice_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance bounded_lattice_hom_class.to_inf_top_hom_class [lattice α] [lattice β]
  [bounded_order α] [bounded_order β] [bounded_lattice_hom_class F α β] :
  inf_top_hom_class F α β :=
{ .. ‹bounded_lattice_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance bounded_lattice_hom_class.to_bounded_order_hom_class [lattice α] [lattice β]
  [bounded_order α] [bounded_order β] [bounded_lattice_hom_class F α β] :
  bounded_order_hom_class F α β :=
{ .. ‹bounded_lattice_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance order_iso.sup_hom_class [semilattice_sup α] [semilattice_sup β] :
  sup_hom_class (α ≃o β) α β :=
{ map_sup := λ f, f.map_sup, ..rel_iso.rel_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso.inf_hom_class [semilattice_inf α] [semilattice_inf β] :
  inf_hom_class (α ≃o β) α β :=
{ map_inf := λ f, f.map_inf, ..rel_iso.rel_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso.lattice_hom_class [lattice α] [lattice β] : lattice_hom_class (α ≃o β) α β :=
{ ..order_iso.sup_hom_class, ..order_iso.inf_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso.bounded_lattice_hom_class [lattice α] [lattice β] [bounded_order α]
  [bounded_order β] :
  bounded_lattice_hom_class (α ≃o β) α β :=
{ ..order_iso.lattice_hom_class, ..order_iso.bounded_order_hom_class }

@[simp] lemma map_finset_sup [semilattice_sup α] [order_bot α] [semilattice_sup β] [order_bot β]
  [sup_bot_hom_class F α β] (f : F) (s : finset ι) (g : ι → α) :
  f (s.sup g) = s.sup (f ∘ g) :=
finset.cons_induction_on s (map_bot f) $ λ i s _ h,
  by rw [finset.sup_cons, finset.sup_cons, map_sup, h]

@[simp] lemma map_finset_inf [semilattice_inf α] [order_top α] [semilattice_inf β] [order_top β]
  [inf_top_hom_class F α β] (f : F) (s : finset ι) (g : ι → α) :
  f (s.inf g) = s.inf (f ∘ g) :=
finset.cons_induction_on s (map_top f) $ λ i s _ h,
  by rw [finset.inf_cons, finset.inf_cons, map_inf, h]

instance [has_sup α] [has_sup β] [sup_hom_class F α β] : has_coe_t F (sup_hom α β) :=
⟨λ f, ⟨f, map_sup f⟩⟩

instance [has_inf α] [has_inf β] [inf_hom_class F α β] : has_coe_t F (inf_hom α β) :=
⟨λ f, ⟨f, map_inf f⟩⟩

instance [has_sup α] [has_sup β] [has_bot α] [has_bot β] [sup_bot_hom_class F α β] :
  has_coe_t F (sup_bot_hom α β) :=
⟨λ f, ⟨f, map_bot f⟩⟩

instance [has_inf α] [has_inf β] [has_top α] [has_top β] [inf_top_hom_class F α β] :
  has_coe_t F (inf_top_hom α β) :=
⟨λ f, ⟨f, map_top f⟩⟩

instance [lattice α] [lattice β] [lattice_hom_class F α β] : has_coe_t F (lattice_hom α β) :=
⟨λ f, { to_fun := f, map_sup' := map_sup f, map_inf' := map_inf f }⟩

instance [lattice α] [lattice β] [bounded_order α] [bounded_order β]
  [bounded_lattice_hom_class F α β] : has_coe_t F (bounded_lattice_hom α β) :=
⟨λ f, { to_fun := f, map_top' := map_top f, map_bot' := map_bot f, ..(f : lattice_hom α β) }⟩

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

lemma cancel_right {g₁ g₂ : sup_hom β γ} {f : sup_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, sup_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : sup_hom β γ} {f₁ f₂ : sup_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, sup_hom.ext $ λ a, hg $
  by rw [←sup_hom.comp_apply, h, sup_hom.comp_apply], congr_arg _⟩

end has_sup

variables (α) [semilattice_sup β]

/-- The constant function as a `sup_hom`. -/
def const (b : β) : sup_hom α β := ⟨λ _, b, λ _ _, sup_idem.symm⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

variables {α}

instance : has_sup (sup_hom α β) :=
⟨λ f g, ⟨f ⊔ g, λ a b, by { rw [pi.sup_apply, map_sup, map_sup], exact sup_sup_sup_comm _ _ _ _ }⟩⟩

instance : semilattice_sup (sup_hom α β) := fun_like.coe_injective.semilattice_sup _ $ λ f g, rfl

instance [has_bot β] : has_bot (sup_hom α β) := ⟨sup_hom.const α ⊥⟩
instance [has_top β] : has_top (sup_hom α β) := ⟨sup_hom.const α ⊤⟩

instance [order_bot β] : order_bot (sup_hom α β) :=
order_bot.lift (coe_fn : _ → α → β) (λ _ _, id) rfl

instance [order_top β] : order_top (sup_hom α β) :=
order_top.lift (coe_fn : _ → α → β) (λ _ _, id) rfl

instance [bounded_order β] : bounded_order (sup_hom α β) :=
bounded_order.lift (coe_fn : _ → α → β) (λ _ _, id) rfl rfl

@[simp] lemma coe_sup (f g : sup_hom α β) : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma coe_bot [has_bot β] : ⇑(⊥ : sup_hom α β) = ⊥ := rfl
@[simp] lemma coe_top [has_top β] : ⇑(⊤ : sup_hom α β) = ⊤ := rfl
@[simp] lemma sup_apply (f g : sup_hom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
@[simp] lemma bot_apply [has_bot β] (a : α) : (⊥ : sup_hom α β) a = ⊥ := rfl
@[simp] lemma top_apply [has_top β] (a : α) : (⊤ : sup_hom α β) a = ⊤ := rfl

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

/-- Copy of an `inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
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

/-- Composition of `inf_hom`s as an `inf_hom`. -/
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

lemma cancel_right {g₁ g₂ : inf_hom β γ} {f : inf_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, inf_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : inf_hom β γ} {f₁ f₂ : inf_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, inf_hom.ext $ λ a, hg $
  by rw [←inf_hom.comp_apply, h, inf_hom.comp_apply], congr_arg _⟩

end has_inf

variables (α) [semilattice_inf β]

/-- The constant function as an `inf_hom`. -/
def const (b : β) : inf_hom α β := ⟨λ _, b, λ _ _, inf_idem.symm⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

variables {α}

instance : has_inf (inf_hom α β) :=
⟨λ f g, ⟨f ⊓ g, λ a b, by { rw [pi.inf_apply, map_inf, map_inf], exact inf_inf_inf_comm _ _ _ _ }⟩⟩

instance : semilattice_inf (inf_hom α β) := fun_like.coe_injective.semilattice_inf _ $ λ f g, rfl

instance [has_bot β] : has_bot (inf_hom α β) := ⟨inf_hom.const α ⊥⟩
instance [has_top β] : has_top (inf_hom α β) := ⟨inf_hom.const α ⊤⟩

instance [order_bot β] : order_bot (inf_hom α β) :=
order_bot.lift (coe_fn : _ → α → β) (λ _ _, id) rfl

instance [order_top β] : order_top (inf_hom α β) :=
order_top.lift (coe_fn : _ → α → β) (λ _ _, id) rfl

instance [bounded_order β] : bounded_order (inf_hom α β) :=
bounded_order.lift (coe_fn : _ → α → β) (λ _ _, id) rfl rfl

@[simp] lemma coe_inf (f g : inf_hom α β) : ⇑(f ⊓ g) = f ⊓ g := rfl
@[simp] lemma coe_bot [has_bot β] : ⇑(⊥ : inf_hom α β) = ⊥ := rfl
@[simp] lemma coe_top [has_top β] : ⇑(⊤ : inf_hom α β) = ⊤ := rfl
@[simp] lemma inf_apply (f g : inf_hom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl
@[simp] lemma bot_apply [has_bot β] (a : α) : (⊥ : inf_hom α β) a = ⊥ := rfl
@[simp] lemma top_apply [has_top β] (a : α) : (⊤ : inf_hom α β) a = ⊤ := rfl

end inf_hom

/-! ### Finitary supremum homomorphisms -/

namespace sup_bot_hom
variables [has_sup α] [has_bot α]

section has_sup
variables [has_sup β] [has_bot β] [has_sup γ] [has_bot γ] [has_sup δ] [has_bot δ]

/-- Reinterpret a `sup_bot_hom` as a `bot_hom`. -/
def to_bot_hom (f : sup_bot_hom α β) : bot_hom α β := { ..f }

instance : sup_bot_hom_class (sup_bot_hom α β) α β :=
{ coe :=  λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_sup := λ f, f.map_sup',
  map_bot := λ f, f.map_bot' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (sup_bot_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : sup_bot_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : sup_bot_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `sup_bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sup_bot_hom α β) (f' : α → β) (h : f' = f) : sup_bot_hom α β :=
{ to_sup_hom := f.to_sup_hom.copy f' h, ..f.to_bot_hom.copy f' h }

variables (α)

/-- `id` as a `sup_bot_hom`. -/
@[simps] protected def id : sup_bot_hom α α := ⟨sup_hom.id α, rfl⟩

instance : inhabited (sup_bot_hom α α) := ⟨sup_bot_hom.id α⟩

@[simp] lemma coe_id : ⇑(sup_bot_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : sup_bot_hom.id α a = a := rfl

/-- Composition of `sup_bot_hom`s as a `sup_bot_hom`. -/
def comp (f : sup_bot_hom β γ) (g : sup_bot_hom α β) : sup_bot_hom α γ :=
{ ..f.to_sup_hom.comp g.to_sup_hom, ..f.to_bot_hom.comp g.to_bot_hom }

@[simp] lemma coe_comp (f : sup_bot_hom β γ) (g : sup_bot_hom α β) : (f.comp g : α → γ) = f ∘ g :=
rfl
@[simp] lemma comp_apply (f : sup_bot_hom β γ) (g : sup_bot_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : sup_bot_hom γ δ) (g : sup_bot_hom β γ) (h : sup_bot_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : sup_bot_hom α β) : f.comp (sup_bot_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : sup_bot_hom α β) : (sup_bot_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : sup_bot_hom β γ} {f : sup_bot_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : sup_bot_hom β γ} {f₁ f₂ : sup_bot_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, sup_bot_hom.ext $ λ a, hg $
  by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end has_sup

variables [semilattice_sup β] [order_bot β]

instance : has_sup (sup_bot_hom α β) :=
⟨λ f g, { to_sup_hom := f.to_sup_hom ⊔ g.to_sup_hom, ..f.to_bot_hom ⊔ g.to_bot_hom }⟩

instance : semilattice_sup (sup_bot_hom α β) :=
fun_like.coe_injective.semilattice_sup _ $ λ f g, rfl

instance : order_bot (sup_bot_hom α β) := { bot := ⟨⊥, rfl⟩, bot_le := λ f, bot_le }

@[simp] lemma coe_sup (f g : sup_bot_hom α β) : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma coe_bot : ⇑(⊥ : sup_bot_hom α β) = ⊥ := rfl
@[simp] lemma sup_apply (f g : sup_bot_hom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
@[simp] lemma bot_apply (a : α) : (⊥ : sup_bot_hom α β) a = ⊥ := rfl

end sup_bot_hom

/-! ### Finitary infimum homomorphisms -/

namespace inf_top_hom
variables [has_inf α] [has_top α]

section has_inf
variables [has_inf β] [has_top β] [has_inf γ] [has_top γ] [has_inf δ] [has_top δ]

/-- Reinterpret an `inf_top_hom` as a `top_hom`. -/
def to_top_hom (f : inf_top_hom α β) : top_hom α β := { ..f }

instance : inf_top_hom_class (inf_top_hom α β) α β :=
{ coe :=  λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_inf := λ f, f.map_inf',
  map_top := λ f, f.map_top' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (inf_top_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : inf_top_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : inf_top_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of an `inf_top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : inf_top_hom α β) (f' : α → β) (h : f' = f) : inf_top_hom α β :=
{ to_inf_hom := f.to_inf_hom.copy f' h, ..f.to_top_hom.copy f' h }

variables (α)

/-- `id` as an `inf_top_hom`. -/
@[simps] protected def id : inf_top_hom α α := ⟨inf_hom.id α, rfl⟩

instance : inhabited (inf_top_hom α α) := ⟨inf_top_hom.id α⟩

@[simp] lemma coe_id : ⇑(inf_top_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : inf_top_hom.id α a = a := rfl

/-- Composition of `inf_top_hom`s as an `inf_top_hom`. -/
def comp (f : inf_top_hom β γ) (g : inf_top_hom α β) : inf_top_hom α γ :=
{ ..f.to_inf_hom.comp g.to_inf_hom, ..f.to_top_hom.comp g.to_top_hom }

@[simp] lemma coe_comp (f : inf_top_hom β γ) (g : inf_top_hom α β) : (f.comp g : α → γ) = f ∘ g :=
rfl
@[simp] lemma comp_apply (f : inf_top_hom β γ) (g : inf_top_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : inf_top_hom γ δ) (g : inf_top_hom β γ) (h : inf_top_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : inf_top_hom α β) : f.comp (inf_top_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : inf_top_hom α β) : (inf_top_hom.id β).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : inf_top_hom β γ} {f : inf_top_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : inf_top_hom β γ} {f₁ f₂ : inf_top_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, inf_top_hom.ext $ λ a, hg $
  by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end has_inf

variables [semilattice_inf β] [order_top β]

instance : has_inf (inf_top_hom α β) :=
⟨λ f g, { to_inf_hom := f.to_inf_hom ⊓ g.to_inf_hom, ..f.to_top_hom ⊓ g.to_top_hom }⟩

instance : semilattice_inf (inf_top_hom α β) :=
fun_like.coe_injective.semilattice_inf _ $ λ f g, rfl

instance : order_top (inf_top_hom α β) := { top := ⟨⊤, rfl⟩, le_top := λ f, le_top }

@[simp] lemma coe_inf (f g : inf_top_hom α β) : ⇑(f ⊓ g) = f ⊓ g := rfl
@[simp] lemma coe_top : ⇑(⊤ : inf_top_hom α β) = ⊤ := rfl
@[simp] lemma inf_apply (f g : inf_top_hom α β) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl
@[simp] lemma top_apply (a : α) : (⊤ : inf_top_hom α β) a = ⊤ := rfl

end inf_top_hom

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
{ .. f.to_sup_hom.copy f' h, .. f.to_inf_hom.copy f' h }

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

lemma cancel_right {g₁ g₂ : lattice_hom β γ} {f : lattice_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, lattice_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : lattice_hom β γ} {f₁ f₂ : lattice_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, lattice_hom.ext $ λ a, hg $
  by rw [←lattice_hom.comp_apply, h, lattice_hom.comp_apply], congr_arg _⟩

/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps] protected def dual :
   lattice_hom α β ≃ lattice_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, { to_fun := to_dual ∘ f ∘ of_dual,
                   map_sup' := λ _ _, congr_arg to_dual (map_inf f _ _),
                   map_inf' := λ _ _, congr_arg to_dual (map_sup f _ _) },
  inv_fun := λ f, { to_fun := of_dual ∘ f ∘ to_dual,
                   map_sup' := λ _ _, congr_arg of_dual (map_inf f _ _),
                   map_inf' := λ _ _, congr_arg of_dual (map_sup f _ _) },
  left_inv := λ f, ext $ λ a, rfl,
  right_inv := λ f, ext $ λ a, rfl }

end lattice_hom

namespace order_hom_class
variables (α β) [linear_order α] [lattice β] [order_hom_class F α β]

/-- An order homomorphism from a linear order is a lattice homomorphism. -/
@[reducible] def to_lattice_hom_class : lattice_hom_class F α β :=
{ map_sup := λ f a b, begin
    obtain h | h := le_total a b,
    { rw [sup_eq_right.2 h, sup_eq_right.2 (order_hom_class.mono f h : f a ≤ f b)] },
    { rw [sup_eq_left.2 h, sup_eq_left.2 (order_hom_class.mono f h : f b ≤ f a)] }
  end,
  map_inf := λ f a b, begin
    obtain h | h := le_total a b,
    { rw [inf_eq_left.2 h, inf_eq_left.2 (order_hom_class.mono f h : f a ≤ f b)] },
    { rw [inf_eq_right.2 h, inf_eq_right.2 (order_hom_class.mono f h : f b ≤ f a)] }
  end,
  .. ‹order_hom_class F α β› }

/-- Reinterpret an order homomorphism to a linear order as a `lattice_hom`. -/
def to_lattice_hom (f : F) : lattice_hom α β :=
by { haveI : lattice_hom_class F α β := order_hom_class.to_lattice_hom_class α β, exact f }

@[simp] lemma coe_to_lattice_hom (f : F) : ⇑(to_lattice_hom α β f) = f := rfl
@[simp] lemma to_lattice_hom_apply (f : F) (a : α) : to_lattice_hom α β f a = f a := rfl

end order_hom_class

/-! ### Bounded lattice homomorphisms -/

namespace bounded_lattice_hom
variables [lattice α] [lattice β] [lattice γ] [lattice δ] [bounded_order α] [bounded_order β]
  [bounded_order γ] [bounded_order δ]

/-- Reinterpret a `bounded_lattice_hom` as a `sup_bot_hom`. -/
def to_sup_bot_hom (f : bounded_lattice_hom α β) : sup_bot_hom α β := { ..f }

/-- Reinterpret a `bounded_lattice_hom` as an `inf_top_hom`. -/
def to_inf_top_hom (f : bounded_lattice_hom α β) : inf_top_hom α β := { ..f }

/-- Reinterpret a `bounded_lattice_hom` as a `bounded_order_hom`. -/
def to_bounded_order_hom (f : bounded_lattice_hom α β) : bounded_order_hom α β :=
{ ..f, ..(f.to_lattice_hom : α →o β) }

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
{ .. f.to_lattice_hom.copy f' h, .. f.to_bounded_order_hom.copy f' h }

variables (α)

/-- `id` as a `bounded_lattice_hom`. -/
protected def id : bounded_lattice_hom α α := { ..lattice_hom.id α, ..bounded_order_hom.id α }

instance : inhabited (bounded_lattice_hom α α) := ⟨bounded_lattice_hom.id α⟩

@[simp] lemma coe_id : ⇑(bounded_lattice_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : bounded_lattice_hom.id α a = a := rfl

/-- Composition of `bounded_lattice_hom`s as a `bounded_lattice_hom`. -/
def comp (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) : bounded_lattice_hom α γ :=
{ ..f.to_lattice_hom.comp g.to_lattice_hom, ..f.to_bounded_order_hom.comp g.to_bounded_order_hom }

@[simp] lemma coe_comp (f : bounded_lattice_hom β γ) (g : bounded_lattice_hom α β) :
  (f.comp g : α → γ) = f ∘ g := rfl
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
  (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, bounded_lattice_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : bounded_lattice_hom β γ} {f₁ f₂ : bounded_lattice_hom α β}
  (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

/-- Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism between the dual
bounded lattices. -/
@[simps] protected def dual :
   bounded_lattice_hom α β ≃ bounded_lattice_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, { to_lattice_hom := f.to_lattice_hom.dual,
                   map_top' := congr_arg to_dual f.map_bot',
                   map_bot' := congr_arg to_dual f.map_top' },
  inv_fun := λ f, { to_lattice_hom := lattice_hom.dual.symm f.to_lattice_hom,
                    map_top' := congr_arg of_dual f.map_bot',
                    map_bot' := congr_arg of_dual f.map_top' },
  left_inv := λ f, ext $ λ a, rfl,
  right_inv := λ f, ext $ λ a, rfl }

end bounded_lattice_hom
