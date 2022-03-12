/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import algebra.order.hom.monoid
import algebra.order.ring
import data.equiv.ring

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `order_ring_hom` : Monotone semiring homomorphisms.
* `order_ring_iso` : Monotone semiring isomorphisms.

## Notation

* `→+*o`: Ordered ring homomorphisms.
* `≃+*o`: Ordered ring isomorphisms.

## Tags

ordered ring homomorphism, order homomorphism
-/

open function

variables {F α β γ δ : Type*}

/-- `order_ring_hom α β` is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : order_ring_hom α β)`,
you should parametrize over `(F : Type*) [order_ring_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_ring_hom_class`. -/
structure order_ring_hom (α β : Type*) [non_assoc_semiring α] [preorder α] [non_assoc_semiring β]
  [preorder β]
  extends α →+* β :=
(monotone' : monotone to_fun)

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc order_ring_hom.to_ring_hom

infix ` →+*o `:25 := order_ring_hom

/-- `order_ring_hom α β` is the type of order-preserving semiring isomorphisms between `α` and `β`.

When possible, instead of parametrizing results over `(f : order_ring_iso α β)`,
you should parametrize over `(F : Type*) [order_ring_iso_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_ring_iso_class`. -/
structure order_ring_iso (α β : Type*) [has_mul α] [has_add α] [has_le α] [has_mul β] [has_add β]
  [has_le β] extends α ≃+* β :=
(map_le_map_iff' {a b : α} : to_fun a ≤ to_fun b ↔ a ≤ b)

infix ` ≃+*o `:25 := order_ring_iso

/-- `order_ring_hom_class F α β` states that `F` is a type of ordered semiring homomorphisms.
You should extend this typeclass when you extend `order_ring_hom`. -/
class order_ring_hom_class (F : Type*) (α β : out_param $ Type*) [non_assoc_semiring α] [preorder α]
  [non_assoc_semiring β] [preorder β] extends ring_hom_class F α β :=
(monotone (f : F) : monotone f)

/-- `order_ring_iso_class F α β` states that `F` is a type of ordered semiring isomorphisms.
You should extend this class when you extend `order_ring_iso`. -/
class order_ring_iso_class (F : Type*) (α β : out_param Type*) [has_mul α] [has_add α] [has_le α]
  [has_mul β] [has_add β] [has_le β]
  extends ring_equiv_class F α β :=
(map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b)

@[priority 100] -- See note [lower priority instance]
instance order_ring_hom_class.to_order_add_monoid_hom_class [non_assoc_semiring α] [preorder α]
  [non_assoc_semiring β] [preorder β] [order_ring_hom_class F α β] :
  order_add_monoid_hom_class F α β :=
{ .. ‹order_ring_hom_class F α β› }

@[priority 100] -- See note [lower priority instance]
instance order_ring_hom_class.to_order_monoid_with_zero_hom_class [non_assoc_semiring α]
  [preorder α] [non_assoc_semiring β] [preorder β] [order_ring_hom_class F α β] :
  order_monoid_with_zero_hom_class F α β :=
{ .. ‹order_ring_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance order_ring_iso_class.to_order_iso_class [has_mul α] [has_add α] [has_le α] [has_mul β]
  [has_add β] [has_le β] [order_ring_iso_class F α β] :
  order_iso_class F α β :=
{ ..‹order_ring_iso_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance order_ring_iso_class.to_order_ring_hom_class [non_assoc_semiring α] [preorder α]
  [non_assoc_semiring β] [preorder β] [order_ring_iso_class F α β] :
  order_ring_hom_class F α β :=
{ monotone := λ f, order_hom_class.mono f, ..‹order_ring_iso_class F α β› }

instance [non_assoc_semiring α] [preorder α] [non_assoc_semiring β] [preorder β]
  [order_ring_hom_class F α β] :
  has_coe_t F (α →+*o β) :=
⟨λ f, ⟨f, order_hom_class.mono f⟩⟩

instance [has_mul α] [has_add α] [has_le α] [has_mul β] [has_add β] [has_le β]
  [order_ring_iso_class F α β] :
  has_coe_t F (α ≃+*o β) :=
⟨λ f, ⟨f, λ a b, map_le_map_iff f⟩⟩

/-! ### Ordered ring homomorphisms -/

namespace order_ring_hom
variables [non_assoc_semiring α] [preorder α]

section preorder
variables [non_assoc_semiring β] [preorder β] [non_assoc_semiring γ] [preorder γ]
  [non_assoc_semiring δ] [preorder δ]

/-- Reinterpret an ordered ring homomorphism as an ordered additive monoid homomorphism. -/
def to_order_add_monoid_hom (f : α →+*o β) : α →+o β := { ..f }

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def to_order_monoid_with_zero_hom (f : α →+*o β) : α →*₀o β := { ..f }

instance : order_ring_hom_class (α →+*o β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr',
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one',
  map_add := λ f, f.map_add',
  map_zero := λ f, f.map_zero',
  monotone := λ f, f.monotone' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →+*o β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

lemma to_fun_eq_coe (f : α →+*o β) : f.to_fun = ⇑f := rfl
@[ext] lemma ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

@[simp] lemma to_ring_hom_eq_coe (f : α →+*o β) : f.to_ring_hom = f := ring_hom.ext $ λ _, rfl
@[simp] lemma to_order_add_monoid_hom_eq_coe (f : α →+*o β) : f.to_order_add_monoid_hom = f := rfl
@[simp] lemma to_order_monoid_with_zero_hom_eq_coe (f : α →+*o β) :
  f.to_order_monoid_with_zero_hom = f := rfl

@[simp] lemma coe_coe_ring_hom (f : α →+*o β) : ⇑(f : α →+* β) = f := rfl
@[simp] lemma coe_coe_order_add_monoid_hom (f : α →+*o β) : ⇑(f : α →+o β) = f := rfl
@[simp] lemma coe_coe_order_monoid_with_zero_hom (f : α →+*o β) : ⇑(f : α →*₀o β) = f := rfl

@[norm_cast] lemma coe_ring_hom_apply (f : α →+*o β) (a : α) : (f : α →+* β) a = f a := rfl
@[norm_cast] lemma coe_order_add_monoid_hom_apply (f : α →+*o β) (a : α) : (f : α →+o β) a = f a :=
rfl
@[norm_cast] lemma coe_order_monoid_with_zero_hom_apply (f : α →+*o β) (a : α) :
  (f : α →*₀o β) a = f a := rfl

/-- Copy of a `order_ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
{ .. f.to_ring_hom.copy f' h, .. f.to_order_add_monoid_hom.copy f' h }

variable (α)

/-- The identity as an ordered ring homomorphism. -/
protected def id : α →+*o α := { ..ring_hom.id _, ..order_hom.id }

instance : inhabited (α →+*o α) := ⟨order_ring_hom.id α⟩

@[simp] lemma coe_id : ⇑(order_ring_hom.id α) = id := rfl

variable {α}

@[simp] lemma id_apply (a : α) : order_ring_hom.id α a = a := rfl

@[simp] lemma coe_ring_hom_id : (order_ring_hom.id α : α →+* α) = ring_hom.id α := rfl
@[simp] lemma coe_order_add_monoid_hom_id :
  (order_ring_hom.id α : α →+o α) = order_add_monoid_hom.id α := rfl
@[simp] lemma coe_order_monoid_with_zero_hom_id :
  (order_ring_hom.id α : α →*₀o α) = order_monoid_with_zero_hom.id α := rfl

/-- Composition of two `order_ring_hom`s as an `order_ring_hom`. -/
protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
{ ..f.to_ring_hom.comp g.to_ring_hom, ..f.to_order_add_monoid_hom.comp g.to_order_add_monoid_hom }

@[simp] lemma coe_comp (f : β →+*o γ) (g : α →+*o β) : ⇑(f.comp g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : β →+*o γ) (g : α →+*o β) (a : α) : f.comp g a = f (g a) := rfl
lemma comp_assoc (f : γ →+*o δ) (g : β →+*o γ) (h : α →+*o β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : α →+*o β) : f.comp (order_ring_hom.id α) = f := ext $ λ x, rfl
@[simp] lemma id_comp (f : α →+*o β) : (order_ring_hom.id β).comp f = f := ext $ λ x, rfl

lemma cancel_right {f₁ f₂ : β →+*o γ} {g : α →+*o β} (hg : surjective g) :
  f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
⟨λ h, ext $ hg.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {f : β →+*o γ} {g₁ g₂ : α →+*o β} (hf : injective f) :
  f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
⟨λ h, ext $ λ a, hf $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end preorder

variables [non_assoc_semiring β]

instance [preorder β] : preorder (order_ring_hom α β) := preorder.lift (coe_fn : _ → α → β)

instance [partial_order β] : partial_order (order_ring_hom α β) :=
partial_order.lift _ fun_like.coe_injective

end order_ring_hom

/-! ### Ordered ring isomorphisms -/

namespace order_ring_iso
section has_le
variables [has_mul α] [has_add α] [has_le α] [has_mul β] [has_add β] [has_le β] [has_mul γ]
  [has_add γ] [has_le γ] [has_mul δ] [has_add δ] [has_le δ]

/-- Reinterpret an ordered ring isomorphism as an order isomorphism. -/
def to_order_iso (f : α ≃+*o β) : α ≃o β := ⟨f.to_ring_equiv.to_equiv, f.map_le_map_iff'⟩

instance : order_ring_iso_class (α ≃+*o β) α β :=
{ coe := λ f, f.to_fun,
  inv := λ f, f.inv_fun,
  coe_injective' := λ f g h₁ h₂, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_add := λ f, f.map_add',
  map_mul := λ f, f.map_mul',
  map_le_map_iff := λ f, f.map_le_map_iff',
  left_inv := λ f, f.left_inv,
  right_inv := λ f, f.right_inv }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α ≃+*o β) (λ _, α → β) := fun_like.has_coe_to_fun

lemma to_fun_eq_coe (f : α ≃+*o β) : f.to_fun = f := rfl

@[ext] lemma ext {f g : α ≃+*o β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

@[simp] lemma coe_mk (e : α ≃+* β) (h) : ⇑(⟨e, h⟩ : α ≃+*o β) = e := rfl
@[simp] lemma mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e := ext $ λ _, rfl

@[simp] lemma to_ring_equiv_eq_coe (f : α ≃+*o β) : f.to_ring_equiv = f := ring_equiv.ext $ λ _, rfl
@[simp] lemma to_order_iso_eq_coe (f : α ≃+*o β) : f.to_order_iso = f := order_iso.ext rfl

@[simp, norm_cast] lemma coe_to_ring_equiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f := rfl
@[simp, norm_cast] lemma coe_to_order_iso (f : α ≃+*o β) : ⇑(f : α ≃o β) = f := rfl

variable (α)

/-- The identity map as an ordered ring isomorphism. -/
@[refl] protected def refl : α ≃+*o α := ⟨ring_equiv.refl α, λ _ _, iff.rfl⟩

instance : inhabited (α ≃+*o α) := ⟨order_ring_iso.refl α⟩

@[simp] lemma refl_apply (x : α) : order_ring_iso.refl α x = x := rfl
@[simp] lemma coe_ring_equiv_refl : (order_ring_iso.refl α : α ≃+* α) = ring_equiv.refl α := rfl
@[simp] lemma coe_order_iso_refl : (order_ring_iso.refl α : α ≃o α) = order_iso.refl α := rfl

variables {α}

/-- The inverse of an ordered ring isomorphism as an ordered ring isomorphism. -/
@[symm] protected def symm (e : α ≃+*o β) : β ≃+*o α :=
⟨e.to_ring_equiv.symm,
  λ a b, by erw [←map_le_map_iff e, e.1.apply_symm_apply, e.1.apply_symm_apply]⟩

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : α ≃+*o β) : β → α := e.symm

@[simp] lemma symm_symm (e : α ≃+*o β) : e.symm.symm = e := ext $ λ _, rfl

/-- Composition of `order_ring_iso`s as an `order_ring_iso`. -/
@[trans, simps] protected def trans (f : α ≃+*o β) (g : β ≃+*o γ) : α ≃+*o γ :=
⟨f.to_ring_equiv.trans g.to_ring_equiv, λ a b, (map_le_map_iff g).trans (map_le_map_iff f)⟩

@[simp] lemma trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a) := rfl

@[simp] lemma self_trans_symm (e : α ≃+*o β) : e.trans e.symm = order_ring_iso.refl α :=
ext e.left_inv
@[simp] lemma symm_trans_self (e : α ≃+*o β) : e.symm.trans e = order_ring_iso.refl β :=
ext e.right_inv

end has_le

section non_assoc_semiring
variables [non_assoc_semiring α] [preorder α] [non_assoc_semiring β] [preorder β]
  [non_assoc_semiring γ] [preorder γ]

/-- Reinterpret an ordered ring isomorphism as an ordered ring homomorphism. -/
def to_order_ring_hom (f : α ≃+*o β) : α →+*o β :=
⟨f.to_ring_equiv.to_ring_hom, λ a b, (map_le_map_iff f).2⟩

@[simp] lemma to_order_ring_hom_eq_coe (f : α ≃+*o β) : f.to_order_ring_hom = f := rfl

@[simp, norm_cast] lemma coe_to_order_ring_hom (f : α ≃+*o β) : ⇑(f : α →+*o β) = f := rfl

@[simp]
lemma coe_to_order_ring_hom_refl : (order_ring_iso.refl α : α →+*o α) = order_ring_hom.id α := rfl

end non_assoc_semiring
end order_ring_iso
