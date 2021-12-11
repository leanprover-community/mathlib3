/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.order.ring
import order.rel_iso
import order.preorder_hom

/-!
# Ordered ring homomorphisms

Homomorphisms between ordered (semi)rings that respect the ordering.

## Main definitions

* `ordered_ring_hom` : A homomorphism `f` between two `ordered_semiring`s that has the property that
  `x ≤ y → f x ≤ f y`.

## Notation

* `→+*o`: order homomorphisms of ordered rings.

## Tags

ordered ring homomorphism, order homomorphism
-/

/-- `ordered_ring_hom R S` is the type of monotone semiring homomorphisms from `R` to `S`.

When possible, instead of parametrizing results over `(f : ordered_ring_hom R S)`,
you should parametrize over `(F : Type*) [ordered_ring_hom_class F R S] (f : F)`.
When you extend this structure, make sure to extend `ordered_ring_hom_class`.
-/
structure ordered_ring_hom (R S : Type*) [ordered_semiring R] [ordered_semiring S]
  extends R →+* S :=
(monotone' : monotone to_fun)

/-- Reinterpret an ordered ring homomorphism as a ring homomorphism. -/
add_decl_doc ordered_ring_hom.to_ring_hom

infix ` →+*o `:25 := ordered_ring_hom

variables {R S : Type*} [ordered_semiring R] [ordered_semiring S]

/-- Reinterpret an ordered ring homomorphism as an order homomorphism. -/
def to_order_hom (f : R →+*o S) : R →ₘ S := { ..f }

/-- `ordered_ring_hom_class F R S` states that `F` is a type of ordered semiring homomorphisms.
You should extend this typeclass when you extend `ordered_ring_hom`. -/
class ordered_ring_hom_class (F : Type*) (R S : out_param $ Type*)
  [ordered_semiring R] [ordered_semiring S] extends ring_hom_class F R S :=
(monotone (f : F) : monotone f)

instance ordered_ring_hom.ordered_ring_hom_class : ordered_ring_hom_class (R →+*o S) R S :=
{ coe := λ f, f,
  coe_injective' := _,
  map_mul := _,
  map_one := _,
  map_add := _,
  map_zero := _,
  monotone := _ }

@[simp] lemma to_ring_hom_eq_coe {f : R →+*o S} : f.to_ring_hom = f := rfl
@[simp] lemma to_order_iso_eq_coe {f : R →+*o S} : f.to_rel_hom = f := rfl
@[simp] lemma coe_ring_hom_to_fun_eq_coe_fun {f : R →+*o S} : (f : R →+* S).to_fun = f := rfl
@[simp] lemma coe_ring_hom_coe_fun_eq_coe_fun {f : R →+*o S} : ((f : R →+* S) : R → S) = f := rfl
@[simp] lemma coe_rel_hom_to_fun_eq_coe_fun {f : R →+*o S} :
  (f : ((≤) : R → R → Prop) →r ((≤) : S → S → Prop)).to_fun = f := rfl
@[simp] lemma coe_rel_hom_coe_fun_eq_coe_fun {f : R →+*o S} :
  ((f : ((≤) : R → R → Prop) →r ((≤) : S → S → Prop)) : R → S) = f := rfl
@[simp]
lemma coe_mul_hom_to_fun_eq_coe_fun {f : R →+*o S} : ((f : R →+* S) : R →* S).to_fun = f := rfl
@[simp]
lemma coe_mul_hom_coe_fun_eq_coe_fun {f : R →+*o S} : (((f : R →+* S) : R →* S) : R → S) = f :=
rfl
@[simp]
lemma coe_add_hom_to_fun_eq_coe_fun {f : R →+*o S} : ((f : R →+* S) : R →+ S).to_fun = f := rfl
@[simp]
lemma coe_add_hom_coe_fun_eq_coe_fun {f : R →+*o S} : (((f : R →+* S) : R →+ S) : R → S) = f :=
rfl

/-- An ordered ring homomorphism preserves multiplication. -/
@[simp] lemma map_mul (e : R →+*o S) (x y : R) : e (x * y) = e x * e y := e.map_mul' x y

/-- An ordered ring homomorphism preserves addition. -/
@[simp] lemma map_add (e : R →+*o S) (x y : R) : e (x + y) = e x + e y := e.map_add' x y

/-- An ordered ring homomorphism preserves ordering. -/
@[simp] lemma map_le (e : R →+*o S) {x y : R} (h : x ≤ y) : e x ≤ e y := e.map_rel' h

alias map_le ← map_rel

protected lemma congr_arg {f : R →+*o S} : Π {x x' : R}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : R →+*o S} (h : f = g) (x : R) : f x = g x := h ▸ rfl

/-- Two ordered ring homomorphisms agree if they are defined by the
  same underlying function. -/
@[ext] lemma ext {f g : R →+*o S} (h : ∀ x, f x = g x) : f = g :=
begin
  cases f, cases g, congr,
  apply ring_hom.ext,
  intro x,
  convert h x,
end

lemma ext_iff {f g : R →+*o S} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, h ▸ rfl, ext⟩

@[norm_cast] lemma coe_ring_hom (f : R →+*o S) (a : R) : (f : R →+* S) a = f a := rfl
@[norm_cast] lemma coe_mul_hom (f : R →+*o S) (a : R) : (f : R →* S) a = f a := rfl
@[norm_cast] lemma coe_add_hom (f : R →+*o S) (a : R) : (f : R →+ S) a = f a := rfl

variable (R)

/-- Identity map is an ordered ring homomorphism. -/
protected def id : R →+*o R :=
{ ..ring_hom.id _,
  ..rel_hom.id _, }

variable {R}
@[simp] lemma id_apply (x : R) : ordered_ring_hom.id R x = x := rfl

@[simp] lemma coe_ring_hom_id : (ordered_ring_hom.id R : R →+* R) = ring_hom.id R := rfl
@[simp] lemma coe_rel_hom_id :
  (ordered_ring_hom.id R : ((≤) : R → R → Prop) →r ((≤) : R → R → Prop)) =
  rel_hom.id ((≤) : R → R → Prop) := rfl

instance : inhabited (R →+*o R) := ⟨ordered_ring_hom.id R⟩

/-- Composition of two ordered ring homomorphisms is an ordered ring homomorphism. -/
protected def comp {T : Type*} [ordered_semiring T] (f₂ : S →+*o T) (f₁ : R →+*o S) : R →+*o T :=
{ ..f₂.to_ring_hom.comp f₁.to_ring_hom,
  ..f₂.to_rel_hom.comp f₁.to_rel_hom, }

-- @[simp] lemma comp_apply {T : Type*} [ordered_semiring T]
--     (f₁ : R →+*o S) (f₂ : S →+*o T) (a : R) : f₂.comp f₁ a = f₂ (f₁ a) := rfl

lemma comp_assoc {T U : Type*} [ordered_semiring T] [ordered_semiring U] (f₁ : R →+*o S)
  (f₂ : S →+*o T) (f₃ : T →+*o U) : (f₃.comp f₂).comp f₁ = f₃.comp (f₂.comp f₁) := rfl

@[simp]
lemma coe_comp {T : Type*} [ordered_semiring T] (f₁ : R →+*o S) (f₂ : S →+*o T) :
  (f₂.comp f₁ : R → T) = f₂ ∘ f₁ := rfl

@[simp] lemma comp_id (f : R →+*o S) : f.comp (ordered_ring_hom.id R) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : R →+*o S) : (ordered_ring_hom.id S).comp f = f := ext $ λ x, rfl

end ordered_ring_hom
