/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import algebra.order.ring
import order.hom.basic

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `order_ring_hom` : A homomorphism `f` between two `ordered_semiring`s that has the property that
  `x ≤ y → f x ≤ f y`.

## Notation

* `→+*o`: Type of ordered ring homomorphisms.

## Tags

ordered ring homomorphism, order homomorphism
-/

variables {F α β : Type*}

/-- `order_ring_hom α β` is the type of monotone semiring homomorphisms from `α` to `β`.

When possible, instead of parametrizing results over `(f : order_ring_hom α β)`,
you should parametrize over `(F : Type*) [order_ring_hom_class F α β] (f : F)`.
When you extend this structure, make sure to extend `order_ring_hom_class`.
-/
structure order_ring_hom (α β : Type*) [ordered_semiring α] [ordered_semiring β]
  extends α →+* β :=
(monotone' : monotone to_fun)

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc order_ring_hom.to_ring_hom

infix ` →+*o `:25 := order_ring_hom

/-- `order_ring_hom_class F α β` states that `F` is a type of ordered semiring homomorphisms.
You should extend this typeclass when you extend `order_ring_hom`. -/
class order_ring_hom_class (F : Type*) (α β : out_param $ Type*)
  [ordered_semiring α] [ordered_semiring β] extends ring_hom_class F α β :=
(monotone (f : F) : monotone f)

instance order_ring_hom_class.to_order_hom_class [ordered_semiring α] [ordered_semiring β]
  [order_ring_hom_class F α β] :
  order_hom_class F α β :=
{ map_rel := order_ring_hom_class.monotone }

instance [ordered_semiring α] [ordered_semiring β] [order_ring_hom_class F α β] :
  has_coe_t F (α →+*o β) :=
⟨λ f, { to_fun := f, map_one' := map_one f, map_mul' := map_mul f, map_add' := map_add f,
  map_zero' := map_zero f, monotone' := order_hom_class.mono f }⟩

namespace order_ring_hom
variables [ordered_semiring α] [ordered_semiring β] {f g : α →+*o β}

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def to_order_hom (f : α →+*o β) : α →o β := { ..f }

instance : order_ring_hom_class (α →+*o β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr',
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one',
  map_add := λ f, f.map_add',
  map_zero := λ f, f.map_zero',
  monotone := λ f, f.monotone' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (α →+*o β) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `order_ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →+*o β) (f' : α → β) (h : f' = f) : α →+*o β :=
{ to_fun := f',
  .. f.to_ring_hom.copy f' $ by { ext, exact congr_fun h _ },
  .. f.to_order_hom.copy f' $ by { ext, exact congr_fun h _ } }

variable (α)

/-- The identity as an ordered ring homomorphism. -/
protected def id : α →+*o α :=
{ monotone' := monotone_id,
  ..ring_hom.id _ }

variable {α}

@[simp] lemma id_apply (x : α) : order_ring_hom.id α x = x := rfl

@[simp] lemma to_ring_hom_id : (order_ring_hom.id α).to_ring_hom = ring_hom.id α := rfl
@[simp] lemma to_order_hom_id : (order_ring_hom.id α).to_order_hom = order_hom.id := rfl

instance : inhabited (α →+*o α) := ⟨order_ring_hom.id α⟩

@[simp] lemma to_ring_hom_eq_coe {f : α →+*o β} : f.to_ring_hom = f := rfl
@[simp] lemma to_order_hom_eq_coe {f : α →+*o β} : f.to_order_hom = f := rfl
@[simp] lemma coe_ring_hom_to_fun_eq_coe_fun {f : α →+*o β} : (f : α →+* β).to_fun = f := rfl
@[simp] lemma coe_ring_hom_coe_fun_eq_coe_fun {f : α →+*o β} : ((f : α →+* β) : α → β) = f := rfl
@[simp] lemma coe_rel_hom_to_fun_eq_coe_fun {f : α →+*o β} :
  (f : ((≤) : α → α → Prop) →r ((≤) : β → β → Prop)).to_fun = f := rfl
@[simp] lemma coe_rel_hom_coe_fun_eq_coe_fun {f : α →+*o β} :
  ((f : ((≤) : α → α → Prop) →r ((≤) : β → β → Prop)) : α → β) = f := rfl
@[simp]
lemma coe_mul_hom_to_fun_eq_coe_fun {f : α →+*o β} : ((f : α →+* β) : α →* β).to_fun = f := rfl
@[simp]
lemma coe_mul_hom_coe_fun_eq_coe_fun {f : α →+*o β} : (((f : α →+* β) : α →* β) : α → β) = f :=
rfl
@[simp]
lemma coe_add_hom_to_fun_eq_coe_fun {f : α →+*o β} : ((f : α →+* β) : α →+ β).to_fun = f := rfl
@[simp]
lemma coe_add_hom_coe_fun_eq_coe_fun {f : α →+*o β} : (((f : α →+* β) : α →+ β) : α → β) = f :=
rfl

protected lemma congr_arg {f : α →+*o β} : Π {x x' : α}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : α →+*o β} (h : f = g) (x : α) : f x = g x := h ▸ rfl

lemma ext_iff {f g : α →+*o β} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, h ▸ rfl, ext⟩

@[norm_cast] lemma coe_ring_hom (f : α →+*o β) (a : α) : (f : α →+* β) a = f a := rfl
@[norm_cast] lemma coe_mul_hom (f : α →+*o β) (a : α) : (f : α →* β) a = f a := rfl
@[norm_cast] lemma coe_add_hom (f : α →+*o β) (a : α) : (f : α →+ β) a = f a := rfl

/-- Composition of two ordered ring homomorphisms is an ordered ring homomorphism. -/
protected def comp {T : Type*} [ordered_semiring T] (f₂ : β →+*o T) (f₁ : α →+*o β) : α →+*o T :=
{ ..f₂.to_ring_hom.comp f₁.to_ring_hom,
  ..f₂.to_rel_hom.comp f₁.to_rel_hom, }

-- @[simp] lemma comp_apply {T : Type*} [ordered_semiring T]
--     (f₁ : α →+*o β) (f₂ : β →+*o T) (a : α) : f₂.comp f₁ a = f₂ (f₁ a) := rfl

lemma comp_assoc {T U : Type*} [ordered_semiring T] [ordered_semiring U] (f₁ : α →+*o β)
  (f₂ : β →+*o T) (f₃ : T →+*o U) : (f₃.comp f₂).comp f₁ = f₃.comp (f₂.comp f₁) := rfl

@[simp]
lemma coe_comp {T : Type*} [ordered_semiring T] (f₁ : α →+*o β) (f₂ : β →+*o T) :
  (f₂.comp f₁ : α → T) = f₂ ∘ f₁ := rfl

@[simp] lemma comp_id (f : α →+*o β) : f.comp (order_ring_hom.id α) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : α →+*o β) : (order_ring_hom.id β).comp f = f := ext $ λ x, rfl

end order_ring_hom
