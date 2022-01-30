/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.complete_lattice
import order.hom.lattice

/-!
# Complete lattice homomorphisms

-/

variables {F α β : Type*}

/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure Sup_hom (α β : Type*) [has_Sup α] [has_Sup β] :=
(to_fun   : α → β)
(map_Sup' (s : set α) : to_fun (Sup s) = Sup (to_fun '' s))

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure Inf_hom (α β : Type*) [has_Inf α] [has_Inf β] :=
(to_fun   : α → β)
(map_Inf' (s : set α) : to_fun (Inf s) = Inf (to_fun '' s))

/-- The type of frame homomorphisms from `α` to `β`. They preserve `⊓` and `⨆`. -/
structure frame_hom (α β : Type*) [complete_lattice α] [complete_lattice β] extends Sup_hom α β :=
(map_inf' (a b : α) : to_fun (a ⊓ b) = to_fun a ⊓ to_fun b)

/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure complete_lattice_hom (α β : Type*) [complete_lattice α] [complete_lattice β]
  extends Sup_hom α β :=
(map_Inf' (s : set α) : to_fun (Inf s) = Inf (to_fun '' s))

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

/-- `frame_hom_class F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `Sup_hom`. -/
class frame_hom_class (F : Type*) (α β : out_param $ Type*) [complete_lattice α]
  [complete_lattice β] extends Sup_hom_class F α β :=
(map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b)

/-- `complete_lattice_hom_class F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class complete_lattice_hom_class (F : Type*) (α β : out_param $ Type*) [complete_lattice α]
  [complete_lattice β] extends Sup_hom_class F α β :=
(map_Inf (f : F) (s : set α) : f (Inf s) = Inf (f '' s))

export Sup_hom_class (map_Sup)
export Inf_hom_class (map_Inf)

attribute [simp] map_Sup map_Inf

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

section semilattice_Inf
variables [semilattice_Inf β] [order_top β] (f g : top_hom α β)

instance : has_Inf (top_hom α β) :=
⟨λ f g, ⟨f ⨅ g, by rw [pi.Inf_apply, map_top, map_top, Inf_top_eq]⟩⟩

instance : semilattice_Inf (top_hom α β) := fun_like.coe_injective.semilattice_Inf _ $ λ _ _, rfl

@[simp] lemma coe_Inf : ⇑(f ⨅ g) = f ⨅ g := rfl
@[simp] lemma Inf_apply (a : α) : (f ⨅ g) a = f a ⨅ g a := rfl

end semilattice_Inf

section semilattice_Sup
variables [semilattice_Sup β] [order_top β] (f g : top_hom α β)

instance : has_Sup (top_hom α β) :=
⟨λ f g, ⟨f ⨆ g, by rw [pi.Sup_apply, map_top, map_top, Sup_top_eq]⟩⟩

instance : semilattice_Sup (top_hom α β) := fun_like.coe_injective.semilattice_Sup _ $ λ _ _, rfl

@[simp] lemma coe_Sup : ⇑(f ⨆ g) = f ⨆ g := rfl
@[simp] lemma Sup_apply (a : α) : (f ⨆ g) a = f a ⨆ g a := rfl

end semilattice_Sup

instance [lattice β] [order_top β] : lattice (top_hom α β) :=
fun_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance [distrib_lattice β] [order_top β] : distrib_lattice (top_hom α β) :=
fun_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

end top_hom

namespace himp_hom
variables [has_himp α]

section has_himp
variables [has_himp β]

instance : himp_hom_class (himp_hom α β) α β :=
{ coe := himp_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_himp := himp_hom.map_himp' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (himp_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : himp_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : himp_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `himp_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : himp_hom α β) (f' : α → β) (h : f' = f) : himp_hom α β :=
{ to_fun := f',
  map_himp' := h.symm ▸ f.map_himp' }

instance : inhabited (himp_hom α β) := ⟨⟨λ _, ⊥, rfl⟩⟩

variables (α)

/-- `id` as a `himp_hom`. -/
protected def id : himp_hom α α := ⟨id, rfl⟩

@[simp] lemma coe_id : ⇑(himp_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : himp_hom.id α a = a := rfl

end has_himp

instance [preorder β] [has_himp β] : preorder (himp_hom α β) :=
preorder.lift (coe_fn : himp_hom α β → α → β)

instance [partial_order β] [has_himp β] : partial_order (himp_hom α β) :=
partial_order.lift _ fun_like.coe_injective

section order_himp
variables [preorder β] [order_himp β]

instance : order_himp (himp_hom α β) := ⟨⟨⊥, rfl⟩, λ _, himp_le⟩

@[simp] lemma coe_himp : ⇑(⊥ : himp_hom α β) = ⊥ := rfl
@[simp] lemma himp_apply (a : α) : (⊥ : himp_hom α β) a = ⊥ := rfl

end order_himp

section semilattice_Inf
variables [semilattice_Inf β] [order_himp β] (f g : himp_hom α β)

instance : has_Inf (himp_hom α β) :=
⟨λ f g, ⟨f ⨅ g, by rw [pi.Inf_apply, map_himp, map_himp, Inf_himp_eq]⟩⟩

instance : semilattice_Inf (himp_hom α β) := fun_like.coe_injective.semilattice_Inf _ $ λ _ _, rfl

@[simp] lemma coe_Inf : ⇑(f ⨅ g) = f ⨅ g := rfl
@[simp] lemma Inf_apply (a : α) : (f ⨅ g) a = f a ⨅ g a := rfl

end semilattice_Inf

section semilattice_Sup
variables [semilattice_Sup β] [order_himp β] (f g : himp_hom α β)

instance : has_Sup (himp_hom α β) :=
⟨λ f g, ⟨f ⨆ g, by rw [pi.Sup_apply, map_himp, map_himp, Sup_himp_eq]⟩⟩

instance : semilattice_Sup (himp_hom α β) := fun_like.coe_injective.semilattice_Sup _ $ λ _ _, rfl

@[simp] lemma coe_Sup : ⇑(f ⨆ g) = f ⨆ g := rfl
@[simp] lemma Sup_apply (a : α) : (f ⨆ g) a = f a ⨆ g a := rfl

end semilattice_Sup

instance [lattice β] [order_himp β] : lattice (himp_hom α β) :=
fun_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance [distrib_lattice β] [order_himp β] : distrib_lattice (himp_hom α β) :=
fun_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

end himp_hom

namespace Sup_hom
variables [has_Sup α]

section has_Sup
variables [has_Sup β]

instance : Sup_hom_class (Sup_hom α β) α β :=
{ coe := Sup_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_Sup := Sup_hom.map_Sup' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (Sup_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : Sup_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : Sup_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `Sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : Sup_hom α β) (f' : α → β) (h : f' = f) : Sup_hom α β :=
{ to_fun := f',
  map_Sup' := h.symm ▸ f.map_Sup' }

variables (α)

/-- `id` as a `Sup_hom`. -/
protected def id : Sup_hom α α := ⟨id, λ a b, rfl⟩

instance : inhabited (Sup_hom α α) := ⟨Sup_hom.id α⟩

@[simp] lemma coe_id : ⇑(Sup_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : Sup_hom.id α a = a := rfl

end has_Sup

variables [semilattice_Sup β]

instance : has_Sup (Sup_hom α β) :=
⟨λ f g, ⟨f ⨆ g, λ a b, by { rw [pi.Sup_apply, map_Sup, map_Sup], exact Sup_Sup_Sup_comm _ _ _ _ }⟩⟩

instance : semilattice_Sup (Sup_hom α β) := fun_like.coe_injective.semilattice_Sup _ $ λ f g, rfl

@[simp] lemma coe_Sup (f g : Sup_hom α β) : ⇑(f ⨆ g) = f ⨆ g := rfl
@[simp] lemma Sup_apply (f g : Sup_hom α β) (a : α): (f ⨆ g) a = f a ⨆ g a := rfl

variables (α)

/-- The constant function as an `Sup_hom`. -/
def const (b : β) : Sup_hom α β := ⟨λ _, b, λ _ _, Sup_idem.symm⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

end Sup_hom

@[priority 100] -- See note [lower instance priority]
instance Sup_hom_class.to_order_hom_class [semilattice_Sup α] [semilattice_Sup β]
  [Sup_hom_class F α β] :
  order_hom_class F α β :=
⟨λ f a b h, by rw [←Sup_eq_right, ←map_Sup, Sup_eq_right.2 h]⟩

namespace Inf_hom
variables [has_Inf α]

section has_Inf
variables [has_Inf β]

instance : Inf_hom_class (Inf_hom α β) α β :=
{ coe := Inf_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_Inf := Inf_hom.map_Inf' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (Inf_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : Inf_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : Inf_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `Inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : Inf_hom α β) (f' : α → β) (h : f' = f) : Inf_hom α β :=
{ to_fun := f',
  map_Inf' := h.symm ▸ f.map_Inf' }

variables (α)

/-- `id` as an `Inf_hom`. -/
protected def id : Inf_hom α α := ⟨id, λ a b, rfl⟩

instance : inhabited (Inf_hom α α) := ⟨Inf_hom.id α⟩

@[simp] lemma coe_id : ⇑(Inf_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : Inf_hom.id α a = a := rfl

end has_Inf

variables [semilattice_Inf β]

instance : has_Inf (Inf_hom α β) :=
⟨λ f g, ⟨f ⨅ g, λ a b, by { rw [pi.Inf_apply, map_Inf, map_Inf], exact Inf_Inf_Inf_comm _ _ _ _ }⟩⟩

instance : semilattice_Inf (Inf_hom α β) := fun_like.coe_injective.semilattice_Inf _ $ λ f g, rfl

@[simp] lemma coe_Inf (f g : Inf_hom α β) : ⇑(f ⨅ g) = f ⨅ g := rfl
@[simp] lemma Inf_apply (f g : Inf_hom α β) (a : α) : (f ⨅ g) a = f a ⨅ g a := rfl

variables (α)

/-- The constant function as an `Inf_hom`. -/
def const (b : β) : Inf_hom α β := ⟨λ _, b, λ _ _, Inf_idem.symm⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

end Inf_hom

@[priority 100] -- See note [lower instance priority]
instance Inf_hom_class.to_order_hom_class [semilattice_Inf α] [semilattice_Inf β]
  [Inf_hom_class F α β] : order_hom_class F α β :=
⟨λ f a b h, by rw [←Inf_eq_left, ←map_Inf, Inf_eq_left.2 h]⟩

namespace frame_hom
variables [lattice α] [lattice β]

/-- Reinterpret a `frame_hom` as an `Inf_hom`. -/
def to_Inf_hom (f : frame_hom α β) : Inf_hom α β := { ..f }

instance : frame_hom_class (frame_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr',
  map_Sup := λ f, f.map_Sup',
  map_Inf := λ f, f.map_Inf' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (frame_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : frame_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : frame_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : frame_hom α β) (f' : α → β) (h : f' = f) : frame_hom α β :=
{ to_fun := f',
  .. f.to_Sup_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_Inf_hom.copy f' $ by { ext, exact congr_fun h _ } }

variables (α)

/-- `id` as a `frame_hom`. -/
protected def id : frame_hom α α :=
{ to_fun := id,
  map_Sup' := λ _ _, rfl,
  map_Inf' := λ _ _, rfl }

instance : inhabited (frame_hom α α) := ⟨frame_hom.id α⟩

@[simp] lemma coe_id : ⇑(frame_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : frame_hom.id α a = a := rfl

end frame_hom

@[priority 100] -- See note [lower instance priority]
instance frame_hom_class.to_Inf_hom_class [lattice α] [lattice β] [frame_hom_class F α β] :
  Inf_hom_class F α β :=
{ .. ‹frame_hom_class F α β› }

namespace complete_lattice_hom
variables [lattice α] [lattice β] [bounded_order α] [bounded_order β]

/-- Reinterpret a `complete_lattice_hom` as a `top_hom`. -/
def to_top_hom (f : complete_lattice_hom α β) : top_hom α β := { ..f }

/-- Reinterpret a `complete_lattice_hom` as a `himp_hom`. -/
def to_himp_hom (f : complete_lattice_hom α β) : himp_hom α β := { ..f }

instance : complete_lattice_hom_class (complete_lattice_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr',
  map_Sup := λ f, f.map_Sup',
  map_Inf := λ f, f.map_Inf',
  map_top := λ f, f.map_top',
  map_himp := λ f, f.map_himp' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (complete_lattice_hom α β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : complete_lattice_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : complete_lattice_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : complete_lattice_hom α β) (f' : α → β) (h : f' = f) :
  complete_lattice_hom α β :=
{ to_fun := f',
  .. f.to_frame_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_top_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_himp_hom.copy f' $ by { ext, exact congr_fun h _ } }

variables (α)

/-- `id` as an `complete_lattice_hom`. -/
protected def id : complete_lattice_hom α α :=
{ to_fun := id,
  map_Sup' := λ _ _, rfl,
  map_Inf' := λ _ _, rfl,
  map_top' := rfl,
  map_himp' := rfl }

instance : inhabited (complete_lattice_hom α α) := ⟨complete_lattice_hom.id α⟩

@[simp] lemma coe_id : ⇑(complete_lattice_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : complete_lattice_hom.id α a = a := rfl

end complete_lattice_hom

@[priority 100] -- See note [lower instance priority]
instance complete_lattice_hom_class.to_top_hom_class [lattice α] [lattice β]
  [bounded_order α] [bounded_order β] [complete_lattice_hom_class F α β] :
  top_hom_class F α β :=
{ .. ‹complete_lattice_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance complete_lattice_hom_class.to_himp_hom_class [lattice α] [lattice β]
  [bounded_order α] [bounded_order β] [complete_lattice_hom_class F α β] :
  himp_hom_class F α β :=
{ .. ‹complete_lattice_hom_class F α β› }
