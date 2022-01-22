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
variables [has_top α] [has_top β]

instance : top_hom_class (top_hom α β) α β :=
{ coe := top_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_top := top_hom.map_top' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (top_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : top_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : top_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : top_hom α β) (f' : α → β) (h : f' = f) : top_hom α β :=
{ to_fun := f',
  map_top' := h.symm ▸ f.map_top' }

instance : inhabited (top_hom α β) := ⟨⟨λ _, ⊤, rfl⟩⟩

end top_hom

namespace bot_hom
variables [has_bot α] [has_bot β]

instance : bot_hom_class (bot_hom α β) α β :=
{ coe := bot_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_bot := bot_hom.map_bot' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (bot_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : bot_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : bot_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : bot_hom α β) (f' : α → β) (h : f' = f) : bot_hom α β :=
{ to_fun := f',
  map_bot' := h.symm ▸ f.map_bot' }

instance : inhabited (bot_hom α β) := ⟨⟨λ _, ⊥, rfl⟩⟩

end bot_hom

namespace sup_hom
variables [has_sup α] [has_sup β]

instance : sup_hom_class (sup_hom α β) α β :=
{ coe := sup_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_sup := sup_hom.map_sup' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (sup_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : sup_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : sup_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sup_hom α β) (f' : α → β) (h : f' = f) : sup_hom α β :=
{ to_fun := f',
  map_sup' := h.symm ▸ f.map_sup' }

/-- `id` as a `sup_hom`. -/
protected def id : sup_hom α α := ⟨id, λ a b, rfl⟩

instance : inhabited (sup_hom α α) := ⟨sup_hom.id⟩

end sup_hom

@[priority 100] -- See note [lower instance priority]
instance sup_hom_class.to_order_hom_class [semilattice_sup α] [semilattice_sup β]
  [sup_hom_class F α β] :
  order_hom_class F α β :=
⟨λ f a b h, by rw [←sup_eq_right, ←map_sup, sup_eq_right.2 h]⟩

namespace inf_hom
variables [has_inf α] [has_inf β]

instance : inf_hom_class (inf_hom α β) α β :=
{ coe := inf_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_inf := inf_hom.map_inf' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (inf_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : inf_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : inf_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : inf_hom α β) (f' : α → β) (h : f' = f) : inf_hom α β :=
{ to_fun := f',
  map_inf' := h.symm ▸ f.map_inf' }

/-- `id` as an `inf_hom`. -/
protected def id : inf_hom α α := ⟨id, λ a b, rfl⟩

instance : inhabited (inf_hom α α) := ⟨inf_hom.id⟩

end inf_hom

@[priority 100] -- See note [lower instance priority]
instance inf_hom_class.to_order_hom_class [semilattice_inf α] [semilattice_inf β]
  [inf_hom_class F α β] : order_hom_class F α β :=
⟨λ f a b h, by rw [←inf_eq_left, ←map_inf, inf_eq_left.2 h]⟩

namespace lattice_hom
variables [lattice α] [lattice β]

/-- Reinterpret a `lattice_hom` as an `inf_hom`-/
def to_inf_hom (f : lattice_hom α β) : inf_hom α β := { ..f }

instance : lattice_hom_class (lattice_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr',
  map_sup := λ f, f.map_sup',
  map_inf := λ f, f.map_inf' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (lattice_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : lattice_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : lattice_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `lattice_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : lattice_hom α β) (f' : α → β) (h : f' = f) : lattice_hom α β :=
{ to_fun := f',
  .. f.to_sup_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_inf_hom.copy f' $ by { ext, exact congr_fun h _ } }

/-- `id` as an `lattice_hom`. -/
protected def id : lattice_hom α α :=
{ to_fun := id,
  map_sup' := λ _ _, rfl,
  map_inf' := λ _ _, rfl }

instance : inhabited (lattice_hom α α) := ⟨lattice_hom.id⟩

end lattice_hom

@[priority 100] -- See note [lower instance priority]
instance lattice_hom_class.to_inf_hom_class [lattice α] [lattice β] [lattice_hom_class F α β] :
  inf_hom_class F α β :=
{ .. ‹lattice_hom_class F α β› }

namespace bounded_lattice_hom
variables [lattice α] [lattice β] [bounded_order α] [bounded_order β]

/-- Reinterpret a `bounded_lattice_hom` as a `top_hom`-/
def to_top_hom (f : bounded_lattice_hom α β) : top_hom α β := { ..f }

/-- Reinterpret a `bounded_lattice_hom` as a `bot_hom`-/
def to_bot_hom (f : bounded_lattice_hom α β) : bot_hom α β := { ..f }

instance : bounded_lattice_hom_class (bounded_lattice_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr',
  map_sup := λ f, f.map_sup',
  map_inf := λ f, f.map_inf',
  map_top := λ f, f.map_top',
  map_bot := λ f, f.map_bot' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (bounded_lattice_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : bounded_lattice_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : bounded_lattice_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bounded_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : bounded_lattice_hom α β) (f' : α → β) (h : f' = f) :
  bounded_lattice_hom α β :=
{ to_fun := f',
  .. f.to_lattice_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_top_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_bot_hom.copy f' $ by { ext, exact congr_fun h _ } }

/-- `id` as an `bounded_lattice_hom`. -/
protected def id : bounded_lattice_hom α α :=
{ to_fun := id,
  map_sup' := λ _ _, rfl,
  map_inf' := λ _ _, rfl,
  map_top' := rfl,
  map_bot' := rfl }

instance : inhabited (bounded_lattice_hom α α) := ⟨bounded_lattice_hom.id⟩

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
