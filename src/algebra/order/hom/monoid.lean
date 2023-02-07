/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.pi.algebra
import algebra.hom.group
import algebra.order.group.instances
import algebra.order.monoid.with_zero.defs
import order.hom.basic

/-!
# Ordered monoid and group homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines morphisms between (additive) ordered monoids.

## Types of morphisms

* `order_add_monoid_hom`: Ordered additive monoid homomorphisms.
* `order_monoid_hom`: Ordered monoid homomorphisms.
* `order_monoid_with_zero_hom`: Ordered monoid with zero homomorphisms.

## Typeclasses

* `order_add_monoid_hom_class`
* `order_monoid_hom_class`
* `order_monoid_with_zero_hom_class`

## Notation

* `→+o`: Bundled ordered additive monoid homs. Also use for additive groups homs.
* `→*o`: Bundled ordered monoid homs. Also use for groups homs.
* `→*₀o`: Bundled ordered monoid with zero homs. Also use for groups with zero homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom as
a function via this coercion.

There is no `order_group_hom` -- the idea is that `order_monoid_hom` is used.
The constructor for `order_monoid_hom` needs a proof of `map_one` as well as `map_mul`; a separate
constructor `order_monoid_hom.mk'` will construct ordered group homs (i.e. ordered monoid homs
between ordered groups) given only a proof that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets. This is done when the
instances can be inferred because they are implicit arguments to the type `order_monoid_hom`. When
they can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

ordered monoid, ordered group, monoid with zero
-/

open function

variables {F α β γ δ : Type*}

section add_monoid

/-- `α →+o β` is the type of monotone functions `α → β` that preserve the `ordered_add_comm_monoid`
structure.

`order_add_monoid_hom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+o β)`,
you should parametrize over `(F : Type*) [order_add_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_add_monoid_hom_class`. -/
structure order_add_monoid_hom (α β : Type*) [preorder α] [preorder β] [add_zero_class α]
  [add_zero_class β] extends α →+ β :=
(monotone' : monotone to_fun)

infixr ` →+o `:25 := order_add_monoid_hom

section
set_option old_structure_cmd true

/-- `order_add_monoid_hom_class F α β` states that `F` is a type of ordered monoid homomorphisms.

You should also extend this typeclass when you extend `order_add_monoid_hom`. -/
@[ancestor add_monoid_hom_class]
class order_add_monoid_hom_class (F : Type*) (α β : out_param $ Type*) [preorder α] [preorder β]
  [add_zero_class α] [add_zero_class β]
  extends add_monoid_hom_class F α β :=
(monotone (f : F) : monotone f)

end

-- Instances and lemmas are defined below through `@[to_additive]`.

end add_monoid

section monoid
variables [preorder α] [preorder β] [mul_one_class α] [mul_one_class β]

/-- `α →*o β` is the type of functions `α → β` that preserve the `ordered_comm_monoid` structure.

`order_monoid_hom` is also used for ordered group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*o β)`,
you should parametrize over `(F : Type*) [order_monoid_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_monoid_hom_class`. -/
@[to_additive]
structure order_monoid_hom (α β : Type*) [preorder α] [preorder β] [mul_one_class α]
  [mul_one_class β]
  extends α →* β :=
(monotone' : monotone to_fun)

infixr ` →*o `:25 := order_monoid_hom

section
set_option old_structure_cmd true

/-- `order_monoid_hom_class F α β` states that `F` is a type of ordered monoid homomorphisms.

You should also extend this typeclass when you extend `order_monoid_hom`. -/
@[ancestor monoid_hom_class, to_additive]
class order_monoid_hom_class (F : Type*) (α β : out_param $ Type*)
  [preorder α] [preorder β] [mul_one_class α] [mul_one_class β]
  extends monoid_hom_class F α β :=
(monotone (f : F) : monotone f)

end

@[priority 100, to_additive] -- See note [lower instance priority]
instance order_monoid_hom_class.to_order_hom_class [order_monoid_hom_class F α β] :
  order_hom_class F α β :=
{ map_rel := order_monoid_hom_class.monotone,
  .. ‹order_monoid_hom_class F α β› }

@[to_additive]
instance [order_monoid_hom_class F α β] : has_coe_t F (α →*o β) :=
⟨λ f, { to_fun := f, map_one' := map_one f, map_mul' := map_mul f,
  monotone' := order_monoid_hom_class.monotone _ }⟩

end monoid

section monoid_with_zero
variables [preorder α] [preorder β] [mul_zero_one_class α] [mul_zero_one_class β]

/-- `order_monoid_with_zero_hom α β` is the type of functions `α → β` that preserve
the `monoid_with_zero` structure.

`order_monoid_with_zero_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →+ β)`,
you should parametrize over `(F : Type*) [order_monoid_with_zero_hom_class F α β] (f : F)`.

When you extend this structure, make sure to extend `order_monoid_with_zero_hom_class`. -/
structure order_monoid_with_zero_hom (α β : Type*) [preorder α] [preorder β]
  [mul_zero_one_class α] [mul_zero_one_class β]
  extends α →*₀ β :=
(monotone' : monotone to_fun)

infixr ` →*₀o `:25 := order_monoid_with_zero_hom

section
set_option old_structure_cmd true

/-- `order_monoid_with_zero_hom_class F α β` states that `F` is a type of
ordered monoid with zero homomorphisms.

You should also extend this typeclass when you extend `order_monoid_with_zero_hom`. -/
class order_monoid_with_zero_hom_class (F : Type*) (α β : out_param $ Type*)
  [preorder α] [preorder β] [mul_zero_one_class α] [mul_zero_one_class β]
  extends monoid_with_zero_hom_class F α β :=
(monotone (f : F) : monotone f)

end

@[priority 100] -- See note [lower instance priority]
instance order_monoid_with_zero_hom_class.to_order_monoid_hom_class
  [order_monoid_with_zero_hom_class F α β] : order_monoid_hom_class F α β :=
{ .. ‹order_monoid_with_zero_hom_class F α β› }

instance [order_monoid_with_zero_hom_class F α β] : has_coe_t F (α →*₀o β) :=
⟨λ f, { to_fun := f, map_one' := map_one f, map_zero' := map_zero f, map_mul' := map_mul f,
  monotone' := order_monoid_with_zero_hom_class.monotone _ }⟩

end monoid_with_zero

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid α] [ordered_add_comm_monoid β] [order_add_monoid_hom_class F α β]
  (f : F) {a : α}
include β

lemma map_nonneg (ha : 0 ≤ a) : 0 ≤ f a := by { rw ←map_zero f, exact order_hom_class.mono _ ha }
lemma map_nonpos (ha : a ≤ 0) : f a ≤ 0 := by { rw ←map_zero f, exact order_hom_class.mono _ ha }

end ordered_add_comm_monoid

section ordered_add_comm_group

variables [ordered_add_comm_group α]
  [ordered_add_comm_monoid β] [add_monoid_hom_class F α β] (f : F)

lemma monotone_iff_map_nonneg : monotone (f : α → β) ↔ ∀ a, 0 ≤ a → 0 ≤ f a :=
⟨λ h a, by { rw ←map_zero f, apply h }, λ h a b hl,
  by { rw [←sub_add_cancel b a, map_add f], exact le_add_of_nonneg_left (h _ $ sub_nonneg.2 hl) }⟩

lemma antitone_iff_map_nonpos : antitone (f : α → β) ↔ ∀ a, 0 ≤ a → f a ≤ 0 :=
monotone_to_dual_comp_iff.symm.trans $ monotone_iff_map_nonneg _
lemma monotone_iff_map_nonpos : monotone (f : α → β) ↔ ∀ a ≤ 0, f a ≤ 0 :=
antitone_comp_of_dual_iff.symm.trans $ antitone_iff_map_nonpos _
lemma antitone_iff_map_nonneg : antitone (f : α → β) ↔ ∀ a ≤ 0, 0 ≤ f a :=
monotone_comp_of_dual_iff.symm.trans $ monotone_iff_map_nonneg _

variable [covariant_class β β (+) (<)]

lemma strict_mono_iff_map_pos : strict_mono (f : α → β) ↔ ∀ a, 0 < a → 0 < f a :=
⟨λ h a, by { rw ←map_zero f, apply h }, λ h a b hl,
  by { rw [←sub_add_cancel b a, map_add f], exact lt_add_of_pos_left _ (h _ $ sub_pos.2 hl) }⟩

lemma strict_anti_iff_map_neg : strict_anti (f : α → β) ↔ ∀ a, 0 < a → f a < 0 :=
strict_mono_to_dual_comp_iff.symm.trans $ strict_mono_iff_map_pos _
lemma strict_mono_iff_map_neg : strict_mono (f : α → β) ↔ ∀ a < 0, f a < 0 :=
strict_anti_comp_of_dual_iff.symm.trans $ strict_anti_iff_map_neg _
lemma strict_anti_iff_map_pos : strict_anti (f : α → β) ↔ ∀ a < 0, 0 < f a :=
strict_mono_comp_of_dual_iff.symm.trans $ strict_mono_iff_map_pos _

end ordered_add_comm_group

namespace order_monoid_hom
section preorder
variables [preorder α] [preorder β] [preorder γ] [preorder δ] [mul_one_class α]
  [mul_one_class β] [mul_one_class γ] [mul_one_class δ] {f g : α →*o β}

@[to_additive]
instance : order_monoid_hom_class (α →*o β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one',
  monotone := λ f, f.monotone' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive "Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly."]
instance : has_coe_to_fun (α →*o β) (λ _, α → β) := fun_like.has_coe_to_fun

-- Other lemmas should be accessed through the `fun_like` API
@[ext, to_additive] lemma ext (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h
@[to_additive] lemma to_fun_eq_coe (f : α →*o β) : f.to_fun = (f : α → β) := rfl
@[simp, to_additive] lemma coe_mk (f : α →* β) (h) : (order_monoid_hom.mk f h : α → β) = f := rfl
@[simp, to_additive] lemma mk_coe (f : α →*o β) (h) : order_monoid_hom.mk (f :  α →* β) h = f :=
by { ext, refl }

/-- Reinterpret an ordered monoid homomorphism as an order homomorphism. -/
@[to_additive "Reinterpret an ordered additive monoid homomorphism as an order homomorphism."]
def to_order_hom (f : α →*o β) : α →o β := { ..f }

@[simp, to_additive] lemma coe_monoid_hom (f : α →*o β) : ((f : α →* β) : α → β) = f := rfl
@[simp, to_additive] lemma coe_order_hom (f : α →*o β) : ((f : α →o β) : α → β) = f := rfl

@[to_additive] lemma to_monoid_hom_injective : injective (to_monoid_hom : _ → α →* β) :=
λ f g h, ext $ by convert fun_like.ext_iff.1 h

@[to_additive] lemma to_order_hom_injective : injective (to_order_hom : _ → α →o β) :=
λ f g h, ext $ by convert fun_like.ext_iff.1 h

/-- Copy of an `order_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive "Copy of an `order_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities."]
protected def copy (f : α →*o β) (f' : α → β) (h : f' = f) : α →*o β :=
{ to_fun := f',
  monotone' := h.symm.subst f.monotone',
  ..f.to_monoid_hom.copy f' h }

@[simp, to_additive] lemma coe_copy (f : α →*o β) (f' : α → β) (h : f' = f) :
  ⇑(f.copy f' h) = f' :=
rfl

@[to_additive] lemma copy_eq (f : α →*o β) (f' : α → β) (h : f' = f) :
  f.copy f' h = f :=
fun_like.ext' h

variables (α)

/-- The identity map as an ordered monoid homomorphism. -/
@[to_additive "The identity map as an ordered additive monoid homomorphism."]
protected def id : α →*o α := { ..monoid_hom.id α, ..order_hom.id }

@[simp, to_additive] lemma coe_id : ⇑(order_monoid_hom.id α) = id := rfl

@[to_additive] instance : inhabited (α →*o α) := ⟨order_monoid_hom.id α⟩

variables {α}

/-- Composition of `order_monoid_hom`s as an `order_monoid_hom`. -/
@[to_additive "Composition of `order_add_monoid_hom`s as an `order_add_monoid_hom`"]
def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
{ ..f.to_monoid_hom.comp (g : α →* β), ..f.to_order_hom.comp (g : α →o β) }

@[simp, to_additive] lemma coe_comp (f : β →*o γ) (g : α →*o β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp, to_additive] lemma comp_apply (f : β →*o γ) (g : α →*o β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp, to_additive] lemma coe_comp_monoid_hom (f : β →*o γ) (g : α →*o β) :
  (f.comp g : α →* γ) = (f : β →* γ).comp g := rfl
@[simp, to_additive] lemma coe_comp_order_hom (f : β →*o γ) (g : α →*o β) :
  (f.comp g : α →o γ) = (f : β →o γ).comp g := rfl
@[simp, to_additive] lemma comp_assoc (f : γ →*o δ) (g : β →*o γ) (h : α →*o β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp, to_additive] lemma comp_id (f : α →*o β) : f.comp (order_monoid_hom.id α) = f :=
ext $ λ a, rfl
@[simp, to_additive] lemma id_comp (f : α →*o β) : (order_monoid_hom.id β).comp f = f :=
ext $ λ a, rfl

@[to_additive]
lemma cancel_right {g₁ g₂ : β →*o γ} {f : α →*o β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

@[to_additive]
lemma cancel_left {g : β →*o γ} {f₁ f₂ : α →*o β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive "`1` is the homomorphism sending all elements to `1`."]
instance : has_one (α →*o β) := ⟨{ monotone' := monotone_const, ..(1 : α →* β) }⟩


@[simp, to_additive] lemma coe_one : ⇑(1 : α →*o β) = 1 := rfl
@[simp, to_additive] lemma one_apply (a : α) : (1 : α →*o β) a = 1 := rfl

@[simp, to_additive] lemma one_comp (f : α →*o β) : (1 : β →*o γ).comp f = 1 := rfl
@[simp, to_additive] lemma comp_one (f : β →*o γ) : f.comp (1 : α →*o β) = 1 :=
by { ext, exact map_one f }

end preorder

section mul
variables [ordered_comm_monoid α] [ordered_comm_monoid β] [ordered_comm_monoid γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
@[to_additive "For two ordered additive monoid morphisms `f` and `g`, their product is the ordered
additive monoid morphism sending `a` to `f a + g a`."]
instance : has_mul (α →*o β) :=
⟨λ f g, { monotone' := f.monotone'.mul' g.monotone', ..(f * g : α →* β) }⟩

@[simp, to_additive] lemma coe_mul (f g : α →*o β) : ⇑(f * g) = f * g := rfl
@[simp, to_additive] lemma mul_apply (f g : α →*o β) (a : α) : (f * g) a = f a * g a := rfl

@[to_additive] lemma mul_comp (g₁ g₂ : β →*o γ) (f : α →*o β) :
  (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
@[to_additive] lemma comp_mul (g : β →*o γ) (f₁ f₂ : α →*o β) :
  g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by { ext, exact map_mul g _ _ }

end mul

section ordered_comm_monoid
variables {hα : ordered_comm_monoid α} {hβ : ordered_comm_monoid β}
include hα hβ

@[simp, to_additive] lemma to_monoid_hom_eq_coe (f : α →*o β) : f.to_monoid_hom = f :=
by { ext, refl }
@[simp, to_additive] lemma to_order_hom_eq_coe (f : α →*o β) : f.to_order_hom = f := rfl

end ordered_comm_monoid

section ordered_comm_group
variables {hα : ordered_comm_group α} {hβ : ordered_comm_group β}
include hα hβ

/-- Makes an ordered group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive "Makes an ordered additive group homomorphism from a proof that the map preserves
addition.",
  simps {fully_applied := ff}]
def mk' (f : α → β) (hf : monotone f) (map_mul : ∀ a b : α, f (a * b) = f a * f b) : α →*o β :=
{ monotone' := hf,
  ..monoid_hom.mk' f map_mul }

end ordered_comm_group
end order_monoid_hom

namespace order_monoid_with_zero_hom
section preorder
variables [preorder α] [preorder β] [preorder γ] [preorder δ] [mul_zero_one_class α]
  [mul_zero_one_class β] [mul_zero_one_class γ] [mul_zero_one_class δ] {f g : α →*₀o β}

instance : order_monoid_with_zero_hom_class (α →*₀o β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one',
  map_zero := λ f, f.map_zero',
  monotone := λ f, f.monotone' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (α →*₀o β) (λ _, α → β) := fun_like.has_coe_to_fun

-- Other lemmas should be accessed through the `fun_like` API
@[ext] lemma ext (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h
lemma to_fun_eq_coe (f : α →*₀o β) : f.to_fun = (f : α → β) := rfl
@[simp] lemma coe_mk (f : α →*₀ β) (h) : (order_monoid_with_zero_hom.mk f h : α → β) = f := rfl
@[simp] lemma mk_coe (f : α →*₀o β) (h) : order_monoid_with_zero_hom.mk (f :  α →*₀ β) h = f :=
by { ext, refl }

/-- Reinterpret an ordered monoid with zero homomorphism as an order monoid homomorphism. -/
def to_order_monoid_hom (f : α →*₀o β) : α →*o β := { ..f }

@[simp] lemma coe_monoid_with_zero_hom (f : α →*₀o β) : ⇑(f : α →*₀ β) = f := rfl
@[simp] lemma coe_order_monoid_hom (f : α →*₀o β) : ⇑(f : α →*o β) = f := rfl

lemma to_order_monoid_hom_injective : injective (to_order_monoid_hom : _ → α →*o β) :=
λ f g h, ext $ by convert fun_like.ext_iff.1 h

lemma to_monoid_with_zero_hom_injective : injective (to_monoid_with_zero_hom : _ → α →*₀ β) :=
λ f g h, ext $ by convert fun_like.ext_iff.1 h

/-- Copy of an `order_monoid_with_zero_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : α →*o β :=
{ to_fun := f',
  .. f.to_order_monoid_hom.copy f' h, .. f.to_monoid_with_zero_hom.copy f' h }

@[simp] lemma coe_copy (f : α →*₀o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : α →*₀o β) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- The identity map as an ordered monoid with zero homomorphism. -/
protected def id : α →*₀o α := { ..monoid_with_zero_hom.id α, ..order_hom.id }

@[simp] lemma coe_id : ⇑(order_monoid_with_zero_hom.id α) = id := rfl

instance : inhabited (α →*₀o α) := ⟨order_monoid_with_zero_hom.id α⟩

variables {α}

/-- Composition of `order_monoid_with_zero_hom`s as an `order_monoid_with_zero_hom`. -/
def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
{ ..f.to_monoid_with_zero_hom.comp (g : α →*₀ β), ..f.to_order_monoid_hom.comp (g : α →*o β) }

@[simp] lemma coe_comp (f : β →*₀o γ) (g : α →*₀o β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : β →*₀o γ) (g : α →*₀o β) (a : α) : (f.comp g) a = f (g a) := rfl
@[simp] lemma coe_comp_monoid_with_zero_hom (f : β →*₀o γ) (g : α →*₀o β) :
  (f.comp g : α →*₀ γ) = (f : β →*₀ γ).comp g := rfl
@[simp] lemma coe_comp_order_monoid_hom (f : β →*₀o γ) (g : α →*₀o β) :
  (f.comp g : α →*o γ) = (f : β →*o γ).comp g := rfl
@[simp] lemma comp_assoc (f : γ →*₀o δ) (g : β →*₀o γ) (h : α →*₀o β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : α →*₀o β) : f.comp (order_monoid_with_zero_hom.id α) = f :=
ext $ λ a, rfl
@[simp] lemma id_comp (f : α →*₀o β) : (order_monoid_with_zero_hom.id β).comp f = f :=
ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : β →*₀o γ} {f : α →*₀o β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : β →*₀o γ} {f₁ f₂ : α →*₀o β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

end preorder

section mul
variables [linear_ordered_comm_monoid_with_zero α] [linear_ordered_comm_monoid_with_zero β]
  [linear_ordered_comm_monoid_with_zero γ]

/-- For two ordered monoid morphisms `f` and `g`, their product is the ordered monoid morphism
sending `a` to `f a * g a`. -/
instance : has_mul (α →*₀o β) :=
⟨λ f g, { monotone' := f.monotone'.mul' g.monotone', ..(f * g : α →*₀ β) }⟩

@[simp] lemma coe_mul (f g : α →*₀o β) : ⇑(f * g) = f * g := rfl
@[simp] lemma mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a := rfl

lemma mul_comp (g₁ g₂ : β →*₀o γ) (f : α →*₀o β) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl
lemma comp_mul (g : β →*₀o γ) (f₁ f₂ : α →*₀o β) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ :=
ext $ λ _, map_mul g _ _

end mul

section linear_ordered_comm_monoid_with_zero
variables {hα : preorder α} {hα' : mul_zero_one_class α} {hβ : preorder β}
  {hβ' : mul_zero_one_class β}
include hα hα' hβ hβ'

@[simp] lemma to_monoid_with_zero_hom_eq_coe (f : α →*₀o β) : f.to_monoid_with_zero_hom = f :=
by { ext, refl }
@[simp] lemma to_order_monoid_hom_eq_coe (f : α →*₀o β) : f.to_order_monoid_hom = f := rfl

end linear_ordered_comm_monoid_with_zero
end order_monoid_with_zero_hom
