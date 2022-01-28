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

variables {F α β : Type*}

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

namespace top_hom
variables [has_top α]

section has_top
variables [has_top β]

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

namespace bot_hom
variables [has_bot α]

section has_bot
variables [has_bot β]

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

namespace sup_hom
variables [has_sup α]

section has_sup
variables [has_sup β]

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

end has_sup

variables [semilattice_sup β]

instance : has_sup (sup_hom α β) :=
⟨λ f g, ⟨f ⊔ g, λ a b, by { rw [pi.sup_apply, map_sup, map_sup], exact sup_sup_sup_comm _ _ _ _ }⟩⟩

instance : semilattice_sup (sup_hom α β) := fun_like.coe_injective.semilattice_sup _ $ λ f g, rfl

@[simp] lemma coe_sup (f g : sup_hom α β) : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma sup_apply (f g : sup_hom α β) (a : α): (f ⊔ g) a = f a ⊔ g a := rfl

variables (α)

/-- The constant function as an `sup_hom`. -/
def const (b : β) : sup_hom α β := ⟨λ _, b, λ _ _, sup_idem.symm⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

end sup_hom

@[priority 100] -- See note [lower instance priority]
instance sup_hom_class.to_order_hom_class [semilattice_sup α] [semilattice_sup β]
  [sup_hom_class F α β] :
  order_hom_class F α β :=
⟨λ f a b h, by rw [←sup_eq_right, ←map_sup, sup_eq_right.2 h]⟩

namespace inf_hom
variables [has_inf α]

section has_inf
variables [has_inf β]

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

@[priority 100] -- See note [lower instance priority]
instance inf_hom_class.to_order_hom_class [semilattice_inf α] [semilattice_inf β]
  [inf_hom_class F α β] : order_hom_class F α β :=
⟨λ f a b h, by rw [←inf_eq_left, ←map_inf, inf_eq_left.2 h]⟩

namespace lattice_hom
variables [lattice α] [lattice β]

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

end lattice_hom

@[priority 100] -- See note [lower instance priority]
instance lattice_hom_class.to_inf_hom_class [lattice α] [lattice β] [lattice_hom_class F α β] :
  inf_hom_class F α β :=
{ .. ‹lattice_hom_class F α β› }

namespace bounded_lattice_hom
variables [lattice α] [lattice β] [bounded_order α] [bounded_order β]

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

/-- `id` as an `bounded_lattice_hom`. -/
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

end bounded_lattice_hom

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
