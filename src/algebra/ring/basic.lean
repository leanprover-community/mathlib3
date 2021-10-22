/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland
-/
import algebra.divisibility
import algebra.regular.basic
import data.set.basic

/-!
# Properties and homomorphisms of semirings and rings

This file proves simple properties of semirings, rings and domains and their unit groups. It also
defines bundled homomorphisms of semirings and rings. As with monoid and groups, we use the same
structure `ring_hom a β`, a.k.a. `α →+* β`, for both homomorphism types.

The unbundled homomorphisms are defined in `deprecated/ring`. They are deprecated and the plan is to
slowly remove them from mathlib.

## Main definitions

ring_hom, nonzero, domain, is_domain

## Notations

→+* for bundled ring homs (also use for semiring homs)

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `semiring_hom` -- the idea is that `ring_hom` is used.
  The constructor for a `ring_hom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `ring_hom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`ring_hom`, `semiring_hom`, `semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`,
`is_domain`, `nonzero`, `units`
-/
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

set_option old_structure_cmd true
open function

/-!
### `distrib` class
-/

/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
@[protect_proj, ancestor has_mul has_add]
class distrib (R : Type*) extends has_mul R, has_add R :=
(left_distrib : ∀ a b c : R, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : R, (a + b) * c = (a * c) + (b * c))

lemma left_distrib [distrib R] (a b c : R) : a * (b + c) = a * b + a * c :=
distrib.left_distrib a b c

alias left_distrib ← mul_add

lemma right_distrib [distrib R] (a b c : R) : (a + b) * c = a * c + b * c :=
distrib.right_distrib a b c

alias right_distrib ← add_mul

/-- Pullback a `distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.distrib {S} [has_mul R] [has_add R] [distrib S]
  (f : R → S) (hf : injective f) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  distrib R :=
{ mul := (*),
  add := (+),
  left_distrib := λ x y z, hf $ by simp only [*, left_distrib],
  right_distrib := λ x y z, hf $ by simp only [*, right_distrib] }

/-- Pushforward a `distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.distrib {S} [distrib R] [has_add S] [has_mul S]
  (f : R → S) (hf : surjective f) (add : ∀ x y, f (x + y) = f x + f y)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  distrib S :=
{ mul := (*),
  add := (+),
  left_distrib := hf.forall₃.2 $ λ x y z, by simp only [← add, ← mul, left_distrib],
  right_distrib := hf.forall₃.2 $ λ x y z, by simp only [← add, ← mul, right_distrib] }

/-!
### Semirings
-/

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
@[protect_proj, ancestor add_comm_monoid distrib mul_zero_class]
class non_unital_non_assoc_semiring (α : Type u) extends
  add_comm_monoid α, distrib α, mul_zero_class α

/-- An associative but not-necessarily unital semiring. -/
@[protect_proj, ancestor non_unital_non_assoc_semiring semigroup_with_zero]
class non_unital_semiring (α : Type u) extends
  non_unital_non_assoc_semiring α, semigroup_with_zero α

/-- A unital but not-necessarily-associative semiring. -/
@[protect_proj, ancestor non_unital_non_assoc_semiring mul_zero_one_class]
class non_assoc_semiring (α : Type u) extends
  non_unital_non_assoc_semiring α, mul_zero_one_class α

/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
@[protect_proj, ancestor non_unital_semiring non_assoc_semiring monoid_with_zero]
class semiring (α : Type u) extends non_unital_semiring α, non_assoc_semiring α, monoid_with_zero α

section injective_surjective_maps

variables [has_zero β] [has_add β] [has_mul β]

/-- Pullback a `non_unital_non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_non_assoc_semiring
  {α : Type u} [non_unital_non_assoc_semiring α]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  non_unital_non_assoc_semiring β :=
{ .. hf.mul_zero_class f zero mul, .. hf.add_comm_monoid f zero add, .. hf.distrib f add mul }

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_unital_semiring
  {α : Type u} [non_unital_semiring α]
  (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  non_unital_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul, .. hf.semigroup_with_zero f zero mul }

/-- Pullback a `non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.non_assoc_semiring
  {α : Type u} [non_assoc_semiring α] [has_one β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  non_assoc_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul, .. hf.mul_one_class f one mul }

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.semiring
  {α : Type u} [semiring α] [has_one β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  semiring β :=
{ .. hf.monoid_with_zero f zero one mul, .. hf.add_comm_monoid f zero add,
  .. hf.distrib f add mul }

/-- Pushforward a `non_unital_non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_non_assoc_semiring
  {α : Type u} [non_unital_non_assoc_semiring α]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  non_unital_non_assoc_semiring β :=
{ .. hf.mul_zero_class f zero mul, .. hf.add_comm_monoid f zero add, .. hf.distrib f add mul }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_unital_semiring
  {α : Type u} [non_unital_semiring α]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  non_unital_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul, .. hf.semigroup_with_zero f zero mul }

/-- Pushforward a `non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.non_assoc_semiring
  {α : Type u} [non_assoc_semiring α] [has_one β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  non_assoc_semiring β :=
{ .. hf.non_unital_non_assoc_semiring f zero add mul, .. hf.mul_one_class f one mul }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.semiring
  {α : Type u} [semiring α] [has_one β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  semiring β :=
{ .. hf.monoid_with_zero f zero one mul, .. hf.add_comm_monoid f zero add,
  .. hf.distrib f add mul }

end injective_surjective_maps

section semiring
variables [semiring α]

lemma one_add_one_eq_two : 1 + 1 = (2 : α) :=
by unfold bit0

theorem two_mul (n : α) : 2 * n = n + n :=
eq.trans (right_distrib 1 1 n) (by simp)

lemma distrib_three_right (a b c d : α) : (a + b + c) * d = a * d + b * d + c * d :=
by simp [right_distrib]

theorem mul_two (n : α) : n * 2 = n + n :=
(left_distrib n 1 1).trans (by simp)

theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
(two_mul _).symm

@[to_additive] lemma mul_ite {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  a * (if P then b else c) = if P then a * b else a * c :=
by split_ifs; refl

@[to_additive] lemma ite_mul {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  (if P then a else b) * c = if P then a * c else b * c :=
by split_ifs; refl

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `∑ x in s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

@[simp] lemma mul_boole {α} [non_assoc_semiring α] (P : Prop) [decidable P] (a : α) :
  a * (if P then 1 else 0) = if P then a else 0 :=
by simp

@[simp] lemma boole_mul {α} [non_assoc_semiring α] (P : Prop) [decidable P] (a : α) :
  (if P then 1 else 0) * a = if P then a else 0 :=
by simp

lemma ite_mul_zero_left {α : Type*} [mul_zero_class α] (P : Prop) [decidable P] (a b : α) :
  ite P (a * b) 0 = ite P a 0 * b :=
by { by_cases h : P; simp [h], }

lemma ite_mul_zero_right {α : Type*} [mul_zero_class α] (P : Prop) [decidable P] (a b : α) :
  ite P (a * b) 0 = a * ite P b 0 :=
by { by_cases h : P; simp [h], }

/-- An element `a` of a semiring is even if there exists `k` such `a = 2*k`. -/
def even (a : α) : Prop := ∃ k, a = 2*k

lemma even_iff_two_dvd {a : α} : even a ↔ 2 ∣ a := iff.rfl

@[simp] lemma range_two_mul (α : Type*) [semiring α] :
  set.range (λ x : α, 2 * x) = {a | even a} :=
by { ext x, simp [even, eq_comm] }

@[simp] lemma even_bit0 (a : α) : even (bit0 a) :=
⟨a, by rw [bit0, two_mul]⟩

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def odd (a : α) : Prop := ∃ k, a = 2*k + 1

@[simp] lemma odd_bit1 (a : α) : odd (bit1 a) :=
⟨a, by rw [bit1, bit0, two_mul]⟩

@[simp] lemma range_two_mul_add_one (α : Type*) [semiring α] :
  set.range (λ x : α, 2 * x + 1) = {a | odd a} :=
by { ext x, simp [odd, eq_comm] }

theorem dvd_add {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
dvd.elim h₁ (λ d hd, dvd.elim h₂ (λ e he, dvd.intro (d + e) (by simp [left_distrib, hd, he])))

end semiring

namespace add_hom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_left {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨(*) r, mul_add r⟩

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps { fully_applied := ff}] def mul_right {R : Type*} [distrib R] (r : R) : add_hom R R :=
⟨λ a, a * r, λ _ _, add_mul _ _ r⟩

end add_hom

namespace add_monoid_hom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := (*) r,
  map_zero' := mul_zero r,
  map_add' := mul_add r }

@[simp] lemma coe_mul_left {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_left r) = (*) r := rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) : R →+ R :=
{ to_fun := λ a, a * r,
  map_zero' := zero_mul r,
  map_add' := λ _ _, add_mul _ _ r }

@[simp] lemma coe_mul_right {R : Type*} [non_unital_non_assoc_semiring R] (r : R) :
  ⇑(mul_right r) = (* r) := rfl

lemma mul_right_apply {R : Type*} [non_unital_non_assoc_semiring R] (a r : R) :
  mul_right r a = a * r := rfl

end add_monoid_hom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `monoid_hom` and `monoid_with_zero_hom` in order to put the fields in a
sensible order, even though `monoid_with_zero_hom` already extends `monoid_hom`. -/
structure ring_hom (α : Type*) (β : Type*) [non_assoc_semiring α] [non_assoc_semiring β]
  extends monoid_hom α β, add_monoid_hom α β, monoid_with_zero_hom α β

infixr ` →+* `:25 := ring_hom

/-- Reinterpret a ring homomorphism `f : R →+* S` as a `monoid_with_zero_hom R S`.
The `simp`-normal form is `(f : monoid_with_zero_hom R S)`. -/
add_decl_doc ring_hom.to_monoid_with_zero_hom

/-- Reinterpret a ring homomorphism `f : R →+* S` as a monoid homomorphism `R →* S`.
The `simp`-normal form is `(f : R →* S)`. -/
add_decl_doc ring_hom.to_monoid_hom

/-- Reinterpret a ring homomorphism `f : R →+* S` as an additive monoid homomorphism `R →+ S`.
The `simp`-normal form is `(f : R →+ S)`. -/
add_decl_doc ring_hom.to_add_monoid_hom

namespace ring_hom

section coe

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/
variables {rα : non_assoc_semiring α} {rβ : non_assoc_semiring β}

include rα rβ

instance : has_coe_to_fun (α →+* β) (λ _, α → β) := ⟨ring_hom.to_fun⟩

initialize_simps_projections ring_hom (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : α →+* β) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : α → β) (h₁ h₂ h₃ h₄) : ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) = f := rfl

instance has_coe_monoid_hom : has_coe (α →+* β) (α →* β) := ⟨ring_hom.to_monoid_hom⟩

@[simp, norm_cast] lemma coe_monoid_hom (f : α →+* β) : ⇑(f : α →* β) = f := rfl

@[simp] lemma to_monoid_hom_eq_coe (f : α →+* β) : f.to_monoid_hom = f := rfl
@[simp] lemma to_monoid_with_zero_hom_eq_coe (f : α →+* β) :
  (f.to_monoid_with_zero_hom : α → β) = f := rfl

@[simp] lemma coe_monoid_hom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →* β) = ⟨f, h₁, h₂⟩ :=
rfl

instance has_coe_add_monoid_hom : has_coe (α →+* β) (α →+ β) := ⟨ring_hom.to_add_monoid_hom⟩

@[simp, norm_cast] lemma coe_add_monoid_hom (f : α →+* β) : ⇑(f : α →+ β) = f := rfl

@[simp] lemma to_add_monoid_hom_eq_coe (f : α →+* β) : f.to_add_monoid_hom = f := rfl

@[simp] lemma coe_add_monoid_hom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨f, h₃, h₄⟩ :=
rfl

end coe

variables [rα : non_assoc_semiring α] [rβ : non_assoc_semiring β]

section
include rα rβ

variables (f : α →+* β) {x y : α} {rα rβ}

theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x :=
congr_arg (λ h : α →+* β, h x) h

theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y :=
congr_arg (λ x : α, f x) h

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext ⦃f g : α →+* β⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

theorem ext_iff {f g : α →+* β} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : ring_hom.mk f h₁ h₂ h₃ h₄ = f :=
ext $ λ _, rfl

theorem coe_add_monoid_hom_injective : function.injective (coe : (α →+* β) → (α →+ β)) :=
λ f g h, ext (λ x, add_monoid_hom.congr_fun h x)

theorem coe_monoid_hom_injective : function.injective (coe : (α →+* β) → (α →* β)) :=
λ f g h, ext (λ x, monoid_hom.congr_fun h x)

/-- Ring homomorphisms map zero to zero. -/
@[simp] lemma map_zero (f : α →+* β) : f 0 = 0 := f.map_zero'

/-- Ring homomorphisms map one to one. -/
@[simp] lemma map_one (f : α →+* β) : f 1 = 1 := f.map_one'

/-- Ring homomorphisms preserve addition. -/
@[simp] lemma map_add (f : α →+* β) (a b : α) : f (a + b) = f a + f b := f.map_add' a b

/-- Ring homomorphisms preserve multiplication. -/
@[simp] lemma map_mul (f : α →+* β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

/-- Ring homomorphisms preserve `bit0`. -/
@[simp] lemma map_bit0 (f : α →+* β) (a : α) : f (bit0 a) = bit0 (f a) := map_add _ _ _

/-- Ring homomorphisms preserve `bit1`. -/
@[simp] lemma map_bit1 (f : α →+* β) (a : α) : f (bit1 a) = bit1 (f a) :=
by simp [bit1]

/-- `f : R →+* S` has a trivial codomain iff `f 1 = 0`. -/
lemma codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 :=
by rw [map_one, eq_comm]

/-- `f : R →+* S` has a trivial codomain iff it has a trivial range. -/
lemma codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ (∀ x, f x = 0) :=
f.codomain_trivial_iff_map_one_eq_zero.trans
  ⟨λ h x, by rw [←mul_one x, map_mul, h, mul_zero], λ h, h 1⟩

/-- `f : R →+* S` has a trivial codomain iff its range is `{0}`. -/
lemma codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ set.range f = {0} :=
f.codomain_trivial_iff_range_trivial.trans
  ⟨ λ h, set.ext (λ y, ⟨λ ⟨x, hx⟩, by simp [←hx, h x], λ hy, ⟨0, by simpa using hy.symm⟩⟩),
    λ h x, set.mem_singleton_iff.mp (h ▸ set.mem_range_self x)⟩

/-- `f : R →+* S` doesn't map `1` to `0` if `S` is nontrivial -/
lemma map_one_ne_zero [nontrivial β] : f 1 ≠ 0 :=
mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

/-- If there is a homomorphism `f : R →+* S` and `S` is nontrivial, then `R` is nontrivial. -/
lemma domain_nontrivial [nontrivial β] : nontrivial α :=
⟨⟨1, 0, mt (λ h, show f 1 = 0, by rw [h, map_zero]) f.map_one_ne_zero⟩⟩


end

lemma is_unit_map [semiring α] [semiring β] (f : α →+* β) {a : α} (h : is_unit a) : is_unit (f a) :=
h.map f.to_monoid_hom

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type*) [non_assoc_semiring α] : α →+* α :=
by refine {to_fun := id, ..}; intros; refl

include rα

instance : inhabited (α →+* α) := ⟨id α⟩

@[simp] lemma id_apply (x : α) : ring_hom.id α x = x := rfl
@[simp] lemma coe_add_monoid_hom_id : (id α : α →+ α) = add_monoid_hom.id α := rfl
@[simp] lemma coe_monoid_hom_id : (id α : α →* α) = monoid_hom.id α := rfl

variable {rγ : non_assoc_semiring γ}
include rβ rγ

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (hnp : β →+* γ) (hmn : α →+* β) : α →+* γ :=
{ to_fun := hnp ∘ hmn,
  map_zero' := by simp,
  map_one' := by simp,
  map_add' := λ x y, by simp,
  map_mul' := λ x y, by simp}

/-- Composition of semiring homomorphisms is associative. -/
lemma comp_assoc {δ} {rδ: non_assoc_semiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn := rfl

lemma comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) : (hnp.comp hmn : α → γ) x =
  (hnp (hmn x)) := rfl

omit rγ

@[simp] lemma comp_id (f : α →+* β) : f.comp (id α) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : α →+* β) : (id β).comp f = f := ext $ λ x, rfl

omit rβ

instance : monoid (α →+* α) :=
{ one := id α,
  mul := comp,
  mul_one := comp_id,
  one_mul := id_comp,
  mul_assoc := λ f g h, comp_assoc _ _ _ }

lemma one_def : (1 : α →+* α) = id α := rfl

@[simp] lemma coe_one : ⇑(1 : α →+* α) = _root_.id := rfl

lemma mul_def (f g : α →+* α) : f * g = f.comp g := rfl

@[simp] lemma coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g := rfl

include rβ rγ

lemma cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ring_hom.ext $ (forall_iff_forall_surj hf).1 (ext_iff.1 h), λ h, h ▸ rfl⟩

lemma cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ring_hom.ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

omit rα rβ rγ

end ring_hom

section semiring

variables [semiring α] {a : α}

@[simp] theorem two_dvd_bit0 : 2 ∣ bit0 a := ⟨a, bit0_eq_two_mul _⟩

lemma ring_hom.map_dvd [semiring β] (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
f.to_monoid_hom.map_dvd

end semiring

/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
@[protect_proj, ancestor semiring comm_monoid]
class comm_semiring (α : Type u) extends semiring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance comm_semiring.to_comm_monoid_with_zero [comm_semiring α] : comm_monoid_with_zero α :=
{ .. comm_semiring.to_comm_monoid α, .. comm_semiring.to_semiring α }

section comm_semiring
variables [comm_semiring α] [comm_semiring β] {a b c : α}

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_semiring [has_zero γ] [has_one γ] [has_add γ] [has_mul γ]
  (f : γ → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semiring γ :=
{ .. hf.semiring f zero one add mul, .. hf.comm_semigroup f mul }

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_semiring [has_zero γ] [has_one γ] [has_add γ] [has_mul γ]
  (f : α → γ) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_semiring γ :=
{ .. hf.semiring f zero one add mul, .. hf.comm_semigroup f mul }

lemma add_mul_self_eq (a b : α) : (a + b) * (a + b) = a*a + 2*a*b + b*b :=
by simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]

end comm_semiring

/-!
### Rings
-/

/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
@[protect_proj, ancestor add_comm_group monoid distrib]
class ring (α : Type u) extends add_comm_group α, monoid α, distrib α

section ring
variables [ring α] {a b c d e : α}

/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
@[priority 200]
instance ring.to_semiring : semiring α :=
{ zero_mul := λ a, add_left_cancel $ show 0 * a + 0 * a = 0 * a + 0,
    by rw [← add_mul, zero_add, add_zero],
  mul_zero := λ a, add_left_cancel $ show a * 0 + a * 0 = a * 0 + 0,
    by rw [← mul_add, add_zero, add_zero],
  ..‹ring α› }

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  ring β :=
{ .. hf.add_comm_group f zero add neg sub, .. hf.monoid f one mul, .. hf.distrib f add mul }

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  ring β :=
{ .. hf.add_comm_group f zero add neg sub, .. hf.monoid f one mul, .. hf.distrib f add mul }

lemma neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
neg_eq_of_add_eq_zero
  begin rw [← right_distrib, add_right_neg, zero_mul] end

lemma neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
neg_eq_of_add_eq_zero
  begin rw [← left_distrib, add_right_neg, mul_zero] end

@[simp] lemma neg_mul_eq_neg_mul_symm (a b : α) : - a * b = - (a * b) :=
eq.symm (neg_mul_eq_neg_mul a b)

@[simp] lemma mul_neg_eq_neg_mul_symm (a b : α) : a * - b = - (a * b) :=
eq.symm (neg_mul_eq_mul_neg a b)

lemma neg_mul_neg (a b : α) : -a * -b = a * b :=
by simp

lemma neg_mul_comm (a b : α) : -a * b = a * -b :=
by simp

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a :=
by simp

lemma mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c :=
by simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub_left_distrib ← mul_sub

lemma mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c :=
by simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias mul_sub_right_distrib ← sub_mul

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
lemma mul_neg_one (a : α) : a * -1 = -a := by simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
lemma neg_one_mul (a : α) : -1 * a = -a := by simp

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
calc
  a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp [add_comm]
    ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin rw h, simp end) (λ h,
                                                  begin rw ← h, simp end)
    ... ↔ (a - b) * e + c = d   : begin simp [sub_mul, sub_add_eq_add_sub] end

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
assume h,
calc
  (a - b) * e + c = (a * e + c) - b * e : begin simp [sub_mul, sub_add_eq_add_sub] end
              ... = d                   : begin rw h, simp [@add_sub_cancel α] end

end ring

namespace units
variables [ring α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : has_neg (units α) := ⟨λu, ⟨-↑u, -↑u⁻¹, by simp, by simp⟩ ⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast] protected theorem coe_neg (u : units α) : (↑-u : α) = -u := rfl

@[simp, norm_cast] protected theorem coe_neg_one : ((-1 : units α) : α) = -1 := rfl

/-- Mapping an element of a ring's unit group to its inverse commutes with mapping this element
    to its additive inverse. -/
@[simp] protected theorem neg_inv (u : units α) : (-u)⁻¹ = -u⁻¹ := rfl

/-- An element of a ring's unit group equals the additive inverse of its additive inverse. -/
@[simp] protected theorem neg_neg (u : units α) : - -u = u :=
units.ext $ neg_neg _

/-- Multiplication of elements of a ring's unit group commutes with mapping the first
    argument to its additive inverse. -/
@[simp] protected theorem neg_mul (u₁ u₂ : units α) : -u₁ * u₂ = -(u₁ * u₂) :=
units.ext $ neg_mul_eq_neg_mul_symm _ _

/-- Multiplication of elements of a ring's unit group commutes with mapping the second argument
    to its additive inverse. -/
@[simp] protected theorem mul_neg (u₁ u₂ : units α) : u₁ * -u₂ = -(u₁ * u₂) :=
units.ext $ (neg_mul_eq_mul_neg _ _).symm

/-- Multiplication of the additive inverses of two elements of a ring's unit group equals
    multiplication of the two original elements. -/
@[simp] protected theorem neg_mul_neg (u₁ u₂ : units α) : -u₁ * -u₂ = u₁ * u₂ := by simp

/-- The additive inverse of an element of a ring's unit group equals the additive inverse of
    one times the original element. -/
protected theorem neg_eq_neg_one_mul (u : units α) : -u = -1 * u := by simp

end units

lemma is_unit.neg [ring α] {a : α} : is_unit a → is_unit (-a)
| ⟨x, hx⟩ := hx ▸ (-x).is_unit

namespace ring_hom

/-- Ring homomorphisms preserve additive inverse. -/
@[simp] theorem map_neg {α β} [ring α] [ring β] (f : α →+* β) (x : α) : f (-x) = -(f x) :=
(f : α →+ β).map_neg x

/-- Ring homomorphisms preserve subtraction. -/
@[simp] theorem map_sub {α β} [ring α] [ring β] (f : α →+* β) (x y : α) :
  f (x - y) = (f x) - (f y) := (f : α →+ β).map_sub x y

/-- A ring homomorphism is injective iff its kernel is trivial. -/
theorem injective_iff {α β} [ring α] [non_assoc_semiring β] (f : α →+* β) :
  function.injective f ↔ (∀ a, f a = 0 → a = 0) :=
(f : α →+ β).injective_iff

/-- A ring homomorphism is injective iff its kernel is trivial. -/
theorem injective_iff' {α β} [ring α] [non_assoc_semiring β] (f : α →+* β) :
  function.injective f ↔ (∀ a, f a = 0 ↔ a = 0) :=
(f : α →+ β).injective_iff'

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' {γ} [non_assoc_semiring α] [ring γ] (f : α →* γ)
  (map_add : ∀ a b : α, f (a + b) = f a + f b) :
  α →+* γ :=
{ to_fun := f,
  .. add_monoid_hom.mk' f map_add, .. f }

end ring_hom

/-- A commutative ring is a `ring` with commutative multiplication. -/
@[protect_proj, ancestor ring comm_semigroup]
class comm_ring (α : Type u) extends ring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance comm_ring.to_comm_semiring [s : comm_ring α] : comm_semiring α :=
{ mul_zero := mul_zero, zero_mul := zero_mul, ..s }

section ring
variables [ring α] {a b c : α}

theorem dvd_neg_of_dvd (h : a ∣ b) : (a ∣ -b) :=
dvd.elim h
  (assume c, assume : b = a * c,
    dvd.intro (-c) (by simp [this]))

theorem dvd_of_dvd_neg (h : a ∣ -b) : (a ∣ b) :=
let t := dvd_neg_of_dvd h in by rwa neg_neg at t

/-- An element a of a ring divides the additive inverse of an element b iff a divides b. -/
@[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

theorem neg_dvd_of_dvd (h : a ∣ b) : -a ∣ b :=
dvd.elim h
  (assume c, assume : b = a * c,
    dvd.intro (-c) (by simp [this]))

theorem dvd_of_neg_dvd (h : -a ∣ b) : a ∣ b :=
let t := neg_dvd_of_dvd h in by rwa neg_neg at t

/-- The additive inverse of an element a of a ring divides another element b iff a divides b. -/
@[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
by { rw sub_eq_add_neg, exact dvd_add h₁ (dvd_neg_of_dvd h₂) }

theorem dvd_add_iff_left (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
⟨λh₂, dvd_add h₂ h, λH, by have t := dvd_sub H h; rwa add_sub_cancel at t⟩

theorem dvd_add_iff_right (h : a ∣ b) : a ∣ c ↔ a ∣ b + c :=
by rw add_comm; exact dvd_add_iff_left h

theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 := (dvd_add_iff_right (@two_dvd_bit0 _ _ a)).symm

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
(dvd_add_iff_left h).symm

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
(dvd_add_iff_right h).symm

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp] lemma dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp] lemma dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
dvd_add_left (dvd_refl a)

lemma dvd_iff_dvd_of_dvd_sub {a b c : α} (h : a ∣ (b - c)) : (a ∣ b ↔ a ∣ c) :=
begin
  split,
  { intro h',
    convert dvd_sub h' h,
    exact eq.symm (sub_sub_self b c) },
  { intro h',
    convert dvd_add h h',
    exact eq_add_of_sub_eq rfl }
end

@[simp] theorem even_neg (a : α) : even (-a) ↔ even a :=
dvd_neg _ _

lemma odd.neg {a : α} (hp : odd a) : odd (-a) :=
begin
  obtain ⟨k, hk⟩ := hp,
  use -(k + 1),
  rw [mul_neg_eq_neg_mul_symm, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add,
    neg_add_cancel_right, ←neg_add, hk],
end

@[simp] lemma odd_neg (a : α) : odd (-a) ↔ odd a :=
⟨λ h, neg_neg a ▸ h.neg, odd.neg⟩

end ring

section comm_ring
variables [comm_ring α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  comm_ring β :=
{ .. hf.ring f zero one add mul neg sub, .. hf.comm_semigroup f mul }

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_ring
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : α → β) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  comm_ring β :=
{ .. hf.ring f zero one add mul neg sub, .. hf.comm_semigroup f mul }

local attribute [simp] add_assoc add_comm add_left_comm mul_comm

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self (a b : α) : a * a - b * b = (a + b) * (a - b) :=
by rw [add_mul, mul_sub, mul_sub, mul_comm a b, sub_add_sub_cancel]

lemma mul_self_sub_one (a : α) : a * a - 1 = (a + 1) * (a - 1) :=
by rw [← mul_self_sub_mul_self, mul_one]

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
lemma Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
  ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
begin
  have : c = -(x * x - b * x) := (neg_eq_of_add_eq_zero h).symm,
  have : c = x * (b - x), by subst this; simp [mul_sub, mul_comm],
  refine ⟨b - x, _, by simp, by rw this⟩,
  rw [this, sub_add, ← sub_mul, sub_self]
end

lemma dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
  k ∣ a * x - b * y :=
begin
  convert dvd_add (hxy.mul_left a) (hab.mul_right y),
  rw [mul_sub_left_distrib, mul_sub_right_distrib],
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left],
end

end comm_ring

lemma succ_ne_self [ring α] [nontrivial α] (a : α) : a + 1 ≠ a :=
λ h, one_ne_zero ((add_right_inj a).mp (by simp [h]))

lemma pred_ne_self [ring α] [nontrivial α] (a : α) : a - 1 ≠ a :=
λ h, one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))

/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
lemma is_left_regular_of_non_zero_divisor [ring α] (k : α)
  (h : ∀ (x : α), k * x = 0 → x = 0) : is_left_regular k :=
begin
  intros x y h',
  rw ←sub_eq_zero,
  refine h _ _,
  rw [mul_sub, sub_eq_zero, h']
end

/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
lemma is_right_regular_of_non_zero_divisor [ring α] (k : α)
  (h : ∀ (x : α), x * k = 0 → x = 0) : is_right_regular k :=
begin
  intros x y h',
  simp only at h',
  rw ←sub_eq_zero,
  refine h _ _,
  rw [sub_mul, sub_eq_zero, h']
end

lemma is_regular_of_ne_zero' [ring α] [no_zero_divisors α] {k : α} (hk : k ≠ 0) :
  is_regular k :=
⟨is_left_regular_of_non_zero_divisor k
  (λ x h, (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk),
 is_right_regular_of_non_zero_divisor k
  (λ x h, (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk)⟩

/-- A domain is a nontrivial ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`.

  This is imlemented as a mixin for `ring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
@[protect_proj] class is_domain (α : Type u) [ring α]
  extends no_zero_divisors α, nontrivial α : Prop

section is_domain
section ring

variables [ring α] [is_domain α]

@[priority 100] -- see Note [lower instance priority]
instance is_domain.to_cancel_monoid_with_zero : cancel_monoid_with_zero α :=
{ mul_left_cancel_of_ne_zero := λ a b c ha,
    @is_regular.left _ _ _ (is_regular_of_ne_zero' ha) _ _,
  mul_right_cancel_of_ne_zero := λ a b c hb,
    @is_regular.right _ _ _ (is_regular_of_ne_zero' hb) _ _,
  .. (infer_instance : semiring α) }

/-- Pullback an `is_domain` instance along an injective function. -/
protected theorem function.injective.is_domain [ring β] (f : β →+* α) (hf : injective f) :
  is_domain β :=
{ .. pullback_nonzero f f.map_zero f.map_one,
  .. hf.no_zero_divisors f f.map_zero f.map_mul }

end ring

section comm_ring

variables [comm_ring α] [is_domain α]

@[priority 100] -- see Note [lower instance priority]
instance is_domain.to_comm_cancel_monoid_with_zero : comm_cancel_monoid_with_zero α :=
{ ..comm_semiring.to_comm_monoid_with_zero, ..is_domain.to_cancel_monoid_with_zero }

lemma mul_self_eq_mul_self_iff {a b : α} : a * a = b * b ↔ a = b ∨ a = -b :=
by rw [← sub_eq_zero, mul_self_sub_mul_self, mul_eq_zero, or_comm, sub_eq_zero,
  add_eq_zero_iff_eq_neg]

lemma mul_self_eq_one_iff {a : α} : a * a = 1 ↔ a = 1 ∨ a = -1 :=
by rw [← mul_self_eq_mul_self_iff, one_mul]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
lemma units.inv_eq_self_iff (u : units α) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
by { rw inv_eq_iff_mul_eq_one, simp only [units.ext_iff], push_cast, exact mul_self_eq_one_iff }

/--
Makes a ring homomorphism from an additive group homomorphism from a commutative ring to an integral
domain that commutes with self multiplication, assumes that two is nonzero and one is sent to one.
-/
def add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero [comm_ring β] (f : β →+ α)
  (h : ∀ x, f (x * x) = f x * f x) (h_two : (2 : α) ≠ 0) (h_one : f 1 = 1) : β →+* α :=
{ map_one' := h_one,
  map_mul' := begin
    intros x y,
    have hxy := h (x + y),
    rw [mul_add, add_mul, add_mul, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mul,
      mul_add, mul_add, ← sub_eq_zero, add_comm, ← sub_sub, ← sub_sub, ← sub_sub,
      mul_comm y x, mul_comm (f y) (f x)] at hxy,
    simp only [add_assoc, add_sub_assoc, add_sub_cancel'_right] at hxy,
    rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero, sub_eq_zero,
      or_iff_not_imp_left] at hxy,
    exact hxy h_two,
  end,
  ..f }

@[simp]
lemma add_monoid_hom.coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero [comm_ring β] (f : β →+ α)
  (h h_two h_one) :
  (f.mk_ring_hom_of_mul_self_of_two_ne_zero h h_two h_one : β → α) = f := rfl

@[simp]
lemma add_monoid_hom.coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero [comm_ring β]
  (f : β →+ α) (h h_two h_one) :
  (f.mk_ring_hom_of_mul_self_of_two_ne_zero h h_two h_one : β →+ α) = f := by {ext, simp}

end comm_ring

end is_domain

namespace ring
variables {M₀ : Type*} [monoid_with_zero M₀]
open_locale classical

/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `ring` namespace for brevity, it requires the weaker assumption
`monoid_with_zero M₀` instead of `ring M₀`. -/
noncomputable def inverse : M₀ → M₀ :=
λ x, if h : is_unit x then ((h.unit⁻¹ : units M₀) : M₀) else 0

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp] lemma inverse_unit (u : units M₀) : inverse (u : M₀) = (u⁻¹ : units M₀) :=
begin
  simp only [units.is_unit, inverse, dif_pos],
  exact units.inv_unique rfl
end

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp] lemma inverse_non_unit (x : M₀) (h : ¬(is_unit x)) : inverse x = 0 := dif_neg h

lemma mul_inverse_cancel (x : M₀) (h : is_unit x) : x * inverse x = 1 :=
by { rcases h with ⟨u, rfl⟩, rw [inverse_unit, units.mul_inv], }

lemma inverse_mul_cancel (x : M₀) (h : is_unit x) : inverse x * x = 1 :=
by { rcases h with ⟨u, rfl⟩, rw [inverse_unit, units.inv_mul], }

lemma mul_inverse_cancel_right (x y : M₀) (h : is_unit x) : y * x * inverse x = y :=
by rw [mul_assoc, mul_inverse_cancel x h, mul_one]

lemma inverse_mul_cancel_right (x y : M₀) (h : is_unit x) : y * inverse x * x = y :=
by rw [mul_assoc, inverse_mul_cancel x h, mul_one]

lemma mul_inverse_cancel_left (x y : M₀) (h : is_unit x) : x * (inverse x * y) = y :=
by rw [← mul_assoc, mul_inverse_cancel x h, one_mul]

lemma inverse_mul_cancel_left (x y : M₀) (h : is_unit x) : inverse x * (x * y) = y :=
by rw [← mul_assoc, inverse_mul_cancel x h, one_mul]

end ring

namespace semiconj_by

@[simp] lemma add_right [distrib R] {a x y x' y' : R}
  (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x + x') (y + y') :=
by simp only [semiconj_by, left_distrib, right_distrib, h.eq, h'.eq]

@[simp] lemma add_left [distrib R] {a b x y : R}
  (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a + b) x y :=
by simp only [semiconj_by, left_distrib, right_distrib, ha.eq, hb.eq]

variables [ring R] {a b x y x' y' : R}

lemma neg_right (h : semiconj_by a x y) : semiconj_by a (-x) (-y) :=
by simp only [semiconj_by, h.eq, neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm]

@[simp] lemma neg_right_iff : semiconj_by a (-x) (-y) ↔ semiconj_by a x y :=
⟨λ h, neg_neg x ▸ neg_neg y ▸ h.neg_right, semiconj_by.neg_right⟩

lemma neg_left (h : semiconj_by a x y) : semiconj_by (-a) x y :=
by simp only [semiconj_by, h.eq, neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm]

@[simp] lemma neg_left_iff : semiconj_by (-a) x y ↔ semiconj_by a x y :=
⟨λ h, neg_neg a ▸ h.neg_left, semiconj_by.neg_left⟩

@[simp] lemma neg_one_right (a : R) : semiconj_by a (-1) (-1) :=
(one_right a).neg_right

@[simp] lemma neg_one_left (x : R) : semiconj_by (-1) x x :=
(semiconj_by.one_left x).neg_left

@[simp] lemma sub_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x - x') (y - y') :=
by simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[simp] lemma sub_left (ha : semiconj_by a x y) (hb : semiconj_by b x y) :
  semiconj_by (a - b) x y :=
by simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

end semiconj_by

namespace commute

@[simp] theorem add_right [distrib R] {a b c : R} :
  commute a b → commute a c → commute a (b + c) :=
semiconj_by.add_right

@[simp] theorem add_left [distrib R] {a b c : R} :
  commute a c → commute b c → commute (a + b) c :=
semiconj_by.add_left

lemma bit0_right [distrib R] {x y : R} (h : commute x y) : commute x (bit0 y) :=
h.add_right h

lemma bit0_left [distrib R] {x y : R} (h : commute x y) : commute (bit0 x) y :=
h.add_left h

lemma bit1_right [semiring R] {x y : R} (h : commute x y) : commute x (bit1 y) :=
h.bit0_right.add_right (commute.one_right x)

lemma bit1_left [semiring R] {x y : R} (h : commute x y) : commute (bit1 x) y :=
h.bit0_left.add_left (commute.one_left y)

variables [ring R] {a b c : R}

theorem neg_right : commute a b → commute a (- b) := semiconj_by.neg_right
@[simp] theorem neg_right_iff : commute a (-b) ↔ commute a b := semiconj_by.neg_right_iff

theorem neg_left : commute a b → commute (- a) b := semiconj_by.neg_left
@[simp] theorem neg_left_iff : commute (-a) b ↔ commute a b := semiconj_by.neg_left_iff

@[simp] theorem neg_one_right (a : R) : commute a (-1) := semiconj_by.neg_one_right a
@[simp] theorem neg_one_left (a : R): commute (-1) a := semiconj_by.neg_one_left a

@[simp] theorem sub_right : commute a b → commute a c → commute a (b - c) := semiconj_by.sub_right
@[simp] theorem sub_left : commute a c → commute b c → commute (a - b) c := semiconj_by.sub_left

end commute
