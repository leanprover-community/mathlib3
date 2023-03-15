/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.group_power.basic
import algebra.hom.equiv.basic
import algebra.hom.units
import data.set.lattice
import data.nat.order.basic

/-!
# Pointwise operations of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

/--
Pointwise monoids (`set`, `finset`, `filter`) have derived pointwise actions of the form
`has_smul α β → has_smul α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_smul_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `set.has_nsmul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/
library_note "pointwise nat action"

open function

variables {F α β γ : Type*}

namespace set

/-! ### `0`/`1` as sets -/

section one
variables [has_one α] {s : set α} {a : α}

/-- The set `1 : set α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The set `0 : set α` is defined as `{0}` in locale `pointwise`."]
protected def has_one : has_one (set α) := ⟨{1}⟩

localized "attribute [instance] set.has_one set.has_zero" in pointwise

@[to_additive] lemma singleton_one : ({1} : set α) = 1 := rfl
@[simp, to_additive] lemma mem_one : a ∈ (1 : set α) ↔ a = 1 := iff.rfl
@[to_additive] lemma one_mem_one : (1 : α) ∈ (1 : set α) := eq.refl _
@[simp, to_additive] lemma one_subset : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff
@[to_additive] lemma one_nonempty : (1 : set α).nonempty := ⟨1, rfl⟩
@[simp, to_additive] lemma image_one {f : α → β} : f '' 1 = {f 1} := image_singleton
@[to_additive] lemma subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 := subset_singleton_iff_eq
@[to_additive] lemma nonempty.subset_one_iff (h : s.nonempty) : s ⊆ 1 ↔ s = 1 :=
h.subset_singleton_iff

/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singleton_one_hom : one_hom α (set α) := ⟨singleton, singleton_one⟩

@[simp, to_additive] lemma coe_singleton_one_hom : (singleton_one_hom : α → set α) = singleton :=
rfl

end one

/-! ### Set negation/inversion -/

section inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`. It i
equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale
`pointwise`. It is equal to `{-x | x ∈ s}`, see `set.image_neg`."]
protected def has_inv [has_inv α] : has_inv (set α) := ⟨preimage has_inv.inv⟩

localized "attribute [instance] set.has_inv set.has_neg" in pointwise

section has_inv
variables {ι : Sort*} [has_inv α] {s t : set α} {a : α}

@[simp, to_additive] lemma mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := iff.rfl
@[simp, to_additive] lemma inv_preimage : has_inv.inv ⁻¹' s = s⁻¹ := rfl
@[simp, to_additive] lemma inv_empty : (∅ : set α)⁻¹ = ∅ := rfl
@[simp, to_additive] lemma inv_univ : (univ : set α)⁻¹ = univ := rfl
@[simp, to_additive] lemma inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := preimage_inter
@[simp, to_additive] lemma union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := preimage_union
@[simp, to_additive] lemma Inter_inv (s : ι → set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ := preimage_Inter
@[simp, to_additive] lemma Union_inv (s : ι → set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ := preimage_Union
@[simp, to_additive] lemma compl_inv : (sᶜ)⁻¹ = (s⁻¹)ᶜ := preimage_compl

end has_inv

section has_involutive_inv
variables [has_involutive_inv α] {s t : set α} {a : α}

@[to_additive] lemma inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]

@[simp, to_additive] lemma nonempty_inv : s⁻¹.nonempty ↔ s.nonempty :=
inv_involutive.surjective.nonempty_preimage

@[to_additive] lemma nonempty.inv (h : s.nonempty) : s⁻¹.nonempty := nonempty_inv.2 h

@[simp, to_additive]
lemma image_inv : has_inv.inv '' s = s⁻¹ :=
congr_fun (image_eq_preimage_of_inverse inv_involutive.left_inverse inv_involutive.right_inverse) _

@[simp, to_additive]
instance : has_involutive_inv (set α) :=
{ inv := has_inv.inv,
  inv_inv := λ s, by { simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id'] } }

@[simp, to_additive]
lemma inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
(equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive] lemma inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by { rw [← inv_subset_inv, inv_inv] }

@[simp, to_additive] lemma inv_singleton (a : α) : ({a} : set α)⁻¹ = {a⁻¹} :=
by rw [←image_inv, image_singleton]

@[simp, to_additive] lemma inv_insert (a : α) (s : set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
by rw [insert_eq, union_inv, inv_singleton, insert_eq]

@[to_additive] lemma inv_range {ι : Sort*} {f : ι → α} : (range f)⁻¹ = range (λ i, (f i)⁻¹) :=
by { rw ←image_inv, exact (range_comp _ _).symm }

open mul_opposite

@[to_additive]
lemma image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ :=
by simp_rw [←image_inv, function.semiconj.set_image op_inv s]

end has_involutive_inv
end inv

open_locale pointwise

/-! ### Set addition/multiplication -/

section has_mul
variables {ι : Sort*} {κ : ι → Sort*} [has_mul α] {s s₁ s₂ t t₁ t₂ u : set α} {a b : α}

/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive "The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in
locale `pointwise`."]
protected def has_mul : has_mul (set α) := ⟨image2 (*)⟩

localized "attribute [instance] set.has_mul set.has_add" in pointwise

@[simp, to_additive]
lemma image2_mul : image2 has_mul.mul s t = s * t := rfl

@[to_additive]
lemma mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a := iff.rfl

@[to_additive] lemma mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t := mem_image2_of_mem

@[to_additive add_image_prod]
lemma image_mul_prod : (λ x : α × α, x.fst * x.snd) '' s ×ˢ t = s * t := image_prod _

@[simp, to_additive] lemma empty_mul : ∅ * s = ∅ := image2_empty_left
@[simp, to_additive] lemma mul_empty : s * ∅ = ∅ := image2_empty_right
@[simp, to_additive] lemma mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp, to_additive] lemma mul_nonempty : (s * t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
@[to_additive] lemma nonempty.mul : s.nonempty → t.nonempty → (s * t).nonempty := nonempty.image2
@[to_additive] lemma nonempty.of_mul_left : (s * t).nonempty → s.nonempty := nonempty.of_image2_left
@[to_additive] lemma nonempty.of_mul_right : (s * t).nonempty → t.nonempty :=
nonempty.of_image2_right
@[simp, to_additive] lemma mul_singleton : s * {b} = (* b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_mul : {a} * t = ((*) a) '' t := image2_singleton_left
@[simp, to_additive] lemma singleton_mul_singleton : ({a} : set α) * {b} = {a * b} :=
image2_singleton

@[to_additive, mono] lemma mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ := image2_subset
@[to_additive] lemma mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ := image2_subset_left
@[to_additive] lemma mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t := image2_subset_right
@[to_additive] lemma mul_subset_iff : s * t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x * y ∈ u := image2_subset_iff

attribute [mono] add_subset_add

@[to_additive] lemma union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t := image2_union_left
@[to_additive] lemma mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ := image2_union_right
@[to_additive] lemma inter_mul_subset : (s₁ ∩ s₂) * t ⊆ s₁ * t ∩ (s₂ * t) :=
image2_inter_subset_left
@[to_additive] lemma mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
image2_inter_subset_right

@[to_additive] lemma Union_mul_left_image : (⋃ a ∈ s, ((*) a) '' t) = s * t := Union_image_left _
@[to_additive] lemma Union_mul_right_image : (⋃ a ∈ t, (* a) '' s) = s * t := Union_image_right _

@[to_additive] lemma Union_mul (s : ι → set α) (t : set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
image2_Union_left _ _ _
@[to_additive] lemma mul_Union (s : set α) (t : ι → set α) : s * (⋃ i, t i) = ⋃ i, s * t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_mul (s : Π i, κ i → set α) (t : set α) : (⋃ i j, s i j) * t = ⋃ i j, s i j * t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma mul_Union₂ (s : set α) (t : Π i, κ i → set α) : s * (⋃ i j, t i j) = ⋃ i j, s * t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_mul_subset (s : ι → set α) (t : set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma mul_Inter_subset (s : set α) (t : ι → set α) : s * (⋂ i, t i) ⊆ ⋂ i, s * t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_mul_subset (s : Π i, κ i → set α) (t : set α) :
  (⋂ i j, s i j) * t ⊆ ⋂ i j, s i j * t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma mul_Inter₂_subset (s : set α) (t : Π i, κ i → set α) :
  s * (⋂ i j, t i j) ⊆ ⋂ i j, s * t i j :=
image2_Inter₂_subset_right _ _ _

/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singleton_mul_hom : α →ₙ* set α := ⟨singleton, λ a b, singleton_mul_singleton.symm⟩

@[simp, to_additive] lemma coe_singleton_mul_hom : (singleton_mul_hom : α → set α) = singleton :=
rfl
@[simp, to_additive] lemma singleton_mul_hom_apply (a : α) : singleton_mul_hom a = {a} := rfl

open mul_opposite

@[simp, to_additive]
lemma image_op_mul : op '' (s * t) = op '' t * op '' s := image_image2_antidistrib op_mul

end has_mul

/-! ### Set subtraction/division -/

section has_div
variables {ι : Sort*} {κ : ι → Sort*} [has_div α] {s s₁ s₂ t t₁ t₂ u : set α} {a b : α}

/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive "The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in
locale `pointwise`."]
protected def has_div : has_div (set α) := ⟨image2 (/)⟩

localized "attribute [instance] set.has_div set.has_sub" in pointwise

@[simp, to_additive]
lemma image2_div : image2 has_div.div s t = s / t := rfl

@[to_additive]
lemma mem_div : a ∈ s / t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x / y = a := iff.rfl

@[to_additive] lemma div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t := mem_image2_of_mem

@[to_additive add_image_prod]
lemma image_div_prod : (λ x : α × α, x.fst / x.snd) '' s ×ˢ t = s / t := image_prod _

@[simp, to_additive] lemma empty_div : ∅ / s = ∅ := image2_empty_left
@[simp, to_additive] lemma div_empty : s / ∅ = ∅ := image2_empty_right
@[simp, to_additive] lemma div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp, to_additive] lemma div_nonempty : (s / t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
@[to_additive] lemma nonempty.div : s.nonempty → t.nonempty → (s / t).nonempty := nonempty.image2
@[to_additive] lemma nonempty.of_div_left : (s / t).nonempty → s.nonempty := nonempty.of_image2_left
@[to_additive] lemma nonempty.of_div_right : (s / t).nonempty → t.nonempty :=
nonempty.of_image2_right
@[simp, to_additive] lemma div_singleton : s / {b} = (/ b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_div : {a} / t = ((/) a) '' t := image2_singleton_left
@[simp, to_additive] lemma singleton_div_singleton : ({a} : set α) / {b} = {a / b} :=
image2_singleton

@[to_additive, mono] lemma div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ := image2_subset
@[to_additive] lemma div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ := image2_subset_left
@[to_additive] lemma div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t := image2_subset_right
@[to_additive] lemma div_subset_iff : s / t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x / y ∈ u := image2_subset_iff

attribute [mono] sub_subset_sub

@[to_additive] lemma union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t := image2_union_left
@[to_additive] lemma div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ := image2_union_right
@[to_additive] lemma inter_div_subset : (s₁ ∩ s₂) / t ⊆ s₁ / t ∩ (s₂ / t) :=
image2_inter_subset_left
@[to_additive] lemma div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
image2_inter_subset_right

@[to_additive] lemma Union_div_left_image : (⋃ a ∈ s, ((/) a) '' t) = s / t := Union_image_left _
@[to_additive] lemma Union_div_right_image : (⋃ a ∈ t, (/ a) '' s) = s / t := Union_image_right _

@[to_additive] lemma Union_div (s : ι → set α) (t : set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
image2_Union_left _ _ _
@[to_additive] lemma div_Union (s : set α) (t : ι → set α) : s / (⋃ i, t i) = ⋃ i, s / t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_div (s : Π i, κ i → set α) (t : set α) : (⋃ i j, s i j) / t = ⋃ i j, s i j / t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma div_Union₂ (s : set α) (t : Π i, κ i → set α) : s / (⋃ i j, t i j) = ⋃ i j, s / t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_div_subset (s : ι → set α) (t : set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma div_Inter_subset (s : set α) (t : ι → set α) : s / (⋂ i, t i) ⊆ ⋂ i, s / t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_div_subset (s : Π i, κ i → set α) (t : set α) :
  (⋂ i j, s i j) / t ⊆ ⋂ i j, s i j / t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma div_Inter₂_subset (s : set α) (t : Π i, κ i → set α) :
  s / (⋂ i j, t i j) ⊆ ⋂ i j, s / t i j :=
image2_Inter₂_subset_right _ _ _

end has_div

open_locale pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action].-/
protected def has_nsmul [has_zero α] [has_add α] : has_smul ℕ (set α) := ⟨nsmul_rec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def has_npow [has_one α] [has_mul α] : has_pow (set α) ℕ := ⟨λ s n, npow_rec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def has_zsmul [has_zero α] [has_add α] [has_neg α] : has_smul ℤ (set α) := ⟨zsmul_rec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `set`. See note [pointwise nat action]. -/
@[to_additive] protected def has_zpow [has_one α] [has_mul α] [has_inv α] : has_pow (set α) ℤ :=
⟨λ s n, zpow_rec n s⟩

localized "attribute [instance] set.has_nsmul set.has_npow set.has_zsmul set.has_zpow" in pointwise

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [semigroup α] : semigroup (set α) :=
{ mul_assoc := λ _ _ _, image2_assoc mul_assoc,
  ..set.has_mul }

/-- `set α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def comm_semigroup [comm_semigroup α] : comm_semigroup (set α) :=
{ mul_comm := λ s t, image2_comm mul_comm
  ..set.semigroup }

section mul_one_class
variables [mul_one_class α]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mul_one_class : mul_one_class (set α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..set.has_one, ..set.has_mul }

localized "attribute [instance] set.mul_one_class set.add_zero_class set.semigroup set.add_semigroup
  set.comm_semigroup set.add_comm_semigroup" in pointwise

@[to_additive] lemma subset_mul_left (s : set α) {t : set α} (ht : (1 : α) ∈ t) : s ⊆ s * t :=
λ x hx, ⟨x, 1, hx, ht, mul_one _⟩

@[to_additive] lemma subset_mul_right {s : set α} (t : set α) (hs : (1 : α) ∈ s) : t ⊆ s * t :=
λ x hx, ⟨1, x, hs, hx, one_mul _⟩

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singleton_monoid_hom : α →* set α := { ..singleton_mul_hom, ..singleton_one_hom }

@[simp, to_additive] lemma coe_singleton_monoid_hom :
  (singleton_monoid_hom : α → set α) = singleton := rfl
@[simp, to_additive] lemma singleton_monoid_hom_apply (a : α) : singleton_monoid_hom a = {a} := rfl

end mul_one_class

section monoid
variables [monoid α] {s t : set α} {a : α} {m n : ℕ}

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : monoid (set α) := { ..set.semigroup, ..set.mul_one_class, ..set.has_npow }

localized "attribute [instance] set.monoid set.add_monoid" in pointwise

@[to_additive] lemma pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
| 0 := by { rw pow_zero, exact one_mem_one }
| (n + 1) := by { rw pow_succ, exact mul_mem_mul ha (pow_mem_pow _) }

@[to_additive] lemma pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
| 0 := by { rw pow_zero, exact subset.rfl }
| (n + 1) := by { rw pow_succ, exact mul_subset_mul hst (pow_subset_pow _) }

@[to_additive] lemma pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n :=
begin
  refine nat.le_induction _ (λ n h ih, _) _,
  { exact subset.rfl },
  { rw pow_succ,
    exact ih.trans (subset_mul_right _ hs) }
end

@[simp, to_additive] lemma empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : set α) ^ n = ∅ :=
by rw [← tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, empty_mul]

@[to_additive] lemma mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩

@[to_additive] lemma univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩

@[simp, to_additive] lemma univ_mul_univ : (univ : set α) * univ = univ :=
mul_univ_of_one_mem $ mem_univ _

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp] lemma nsmul_univ {α : Type*} [add_monoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (univ : set α) = univ
| 0 := λ h, (h rfl).elim
| 1 := λ _, one_nsmul _
| (n + 2) := λ _, by { rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ] }

@[simp, to_additive nsmul_univ] lemma univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : set α) ^ n = univ
| 0 := λ h, (h rfl).elim
| 1 := λ _, pow_one _
| (n + 2) := λ _, by { rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ] }

@[to_additive] protected lemma _root_.is_unit.set : is_unit a → is_unit ({a} : set α) :=
is_unit.map (singleton_monoid_hom : α →* set α)

end monoid

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def comm_monoid [comm_monoid α] : comm_monoid (set α) :=
{ ..set.monoid, ..set.comm_semigroup }

localized "attribute [instance] set.comm_monoid set.add_comm_monoid" in pointwise

open_locale pointwise

section division_monoid
variables [division_monoid α] {s t : set α}

@[to_additive] protected lemma mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 :=
begin
  refine ⟨λ h, _, _⟩,
  { have hst : (s * t).nonempty := h.symm.subst one_nonempty,
    obtain ⟨a, ha⟩ := hst.of_image2_left,
    obtain ⟨b, hb⟩ := hst.of_image2_right,
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) :=
      λ a b ha hb, (h.subset $ mem_image2_of_mem ha hb),
    refine ⟨a, b, _, _, H ha hb⟩; refine eq_singleton_iff_unique_mem.2 ⟨‹_›, λ x hx, _⟩,
    { exact (eq_inv_of_mul_eq_one_left $ H hx hb).trans (inv_eq_of_mul_eq_one_left $ H ha hb) },
    { exact (eq_inv_of_mul_eq_one_right $ H ha hx).trans (inv_eq_of_mul_eq_one_right $ H ha hb) } },
  { rintro ⟨b, c, rfl, rfl, h⟩,
    rw [singleton_mul_singleton, h, singleton_one] }
end

/-- `set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`set α` is a subtraction monoid under pointwise operations if `α` is."]
protected def division_monoid : division_monoid (set α) :=
{ mul_inv_rev := λ s t, by { simp_rw ←image_inv, exact image_image2_antidistrib mul_inv_rev },
  inv_eq_of_mul := λ s t h, begin
    obtain ⟨a, b, rfl, rfl, hab⟩ := set.mul_eq_one_iff.1 h,
    rw [inv_singleton, inv_eq_of_mul_eq_one_right hab],
  end,
  div_eq_mul_inv := λ s t,
    by { rw [←image_id (s / t), ←image_inv], exact image_image2_distrib_right div_eq_mul_inv },
  ..set.monoid, ..set.has_involutive_inv, ..set.has_div, ..set.has_zpow }

@[simp, to_additive] lemma is_unit_iff : is_unit s ↔ ∃ a, s = {a} ∧ is_unit a :=
begin
  split,
  { rintro ⟨u, rfl⟩,
    obtain ⟨a, b, ha, hb, h⟩ := set.mul_eq_one_iff.1 u.mul_inv,
    refine ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩,
    rw [←singleton_mul_singleton, ←ha, ←hb],
    exact u.inv_mul },
  { rintro ⟨a, rfl, ha⟩,
    exact ha.set }
end

end division_monoid

/-- `set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtraction_comm_monoid "`set α` is a commutative subtraction monoid under pointwise
operations if `α` is."]
protected def division_comm_monoid [division_comm_monoid α] : division_comm_monoid (set α) :=
{ ..set.division_monoid, ..set.comm_semigroup }

/-- `set α` has distributive negation if `α` has. -/
protected def has_distrib_neg [has_mul α] [has_distrib_neg α] : has_distrib_neg (set α) :=
{ neg_mul := λ _ _, by { simp_rw ←image_neg, exact image2_image_left_comm neg_mul },
  mul_neg := λ _ _, by { simp_rw ←image_neg, exact image_image2_right_comm mul_neg },
  ..set.has_involutive_neg }

localized "attribute [instance] set.division_monoid set.subtraction_monoid set.division_comm_monoid
  set.subtraction_comm_monoid set.has_distrib_neg" in pointwise

section distrib
variables [distrib α] (s t u : set α)

/-!
Note that `set α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/

lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u := image2_distrib_subset_left mul_add
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u := image2_distrib_subset_right add_mul

end distrib

section mul_zero_class
variables [mul_zero_class α] {s t : set α}

/-! Note that `set` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/

lemma mul_zero_subset (s : set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
lemma zero_mul_subset (s : set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]

lemma nonempty.mul_zero (hs : s.nonempty) : s * 0 = 0 :=
s.mul_zero_subset.antisymm $ by simpa [mem_mul] using hs

lemma nonempty.zero_mul (hs : s.nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm $ by simpa [mem_mul] using hs

end mul_zero_class

section group
variables [group α] {s t : set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/

@[simp, to_additive] lemma one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬ disjoint s t :=
by simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, set.nonempty]

@[to_additive] lemma not_one_mem_div_iff : (1 : α) ∉ s / t ↔ disjoint s t :=
one_mem_div_iff.not_left

alias not_one_mem_div_iff ↔ _ _root_.disjoint.one_not_mem_div_set

attribute [to_additive] disjoint.one_not_mem_div_set

@[to_additive] lemma nonempty.one_mem_div (h : s.nonempty) : (1 : α) ∈ s / s :=
let ⟨a, ha⟩ := h in mem_div.2 ⟨a, a, ha, ha, div_self' _⟩

@[to_additive] lemma is_unit_singleton (a : α) : is_unit ({a} : set α) := (group.is_unit a).set

@[simp, to_additive] lemma is_unit_iff_singleton : is_unit s ↔ ∃ a, s = {a} :=
by simp only [is_unit_iff, group.is_unit, and_true]

@[simp, to_additive] lemma image_mul_left : ((*) a) '' t = ((*) a⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[simp, to_additive] lemma image_mul_right : (* b) '' t = (* b⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[to_additive] lemma image_mul_left' : (λ b, a⁻¹ * b) '' t = (λ b, a * b) ⁻¹' t := by simp
@[to_additive] lemma image_mul_right' : (* b⁻¹) '' t = (* b) ⁻¹' t := by simp

@[simp, to_additive] lemma preimage_mul_left_singleton : ((*) a) ⁻¹' {b} = {a⁻¹ * b} :=
by rw [← image_mul_left', image_singleton]

@[simp, to_additive] lemma preimage_mul_right_singleton : (* a) ⁻¹' {b} = {b * a⁻¹} :=
by rw [← image_mul_right', image_singleton]

@[simp, to_additive] lemma preimage_mul_left_one : ((*) a) ⁻¹' 1 = {a⁻¹} :=
by rw [← image_mul_left', image_one, mul_one]

@[simp, to_additive] lemma preimage_mul_right_one : (* b) ⁻¹' 1 = {b⁻¹} :=
by rw [← image_mul_right', image_one, one_mul]

@[to_additive] lemma preimage_mul_left_one' : (λ b, a⁻¹ * b) ⁻¹' 1 = {a} := by simp
@[to_additive] lemma preimage_mul_right_one' : (* b⁻¹) ⁻¹' 1 = {b} := by simp

@[simp, to_additive] lemma mul_univ (hs : s.nonempty) : s * (univ : set α) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩

@[simp, to_additive] lemma univ_mul (ht : t.nonempty) : (univ : set α) * t = univ :=
let ⟨a, ha⟩ := ht in eq_univ_of_forall $ λ b, ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩

end group

section group_with_zero
variables [group_with_zero α] {s t : set α}

lemma div_zero_subset (s : set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
lemma zero_div_subset (s : set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]

lemma nonempty.div_zero (hs : s.nonempty) : s / 0 = 0 :=
s.div_zero_subset.antisymm $ by simpa [mem_div] using hs

lemma nonempty.zero_div (hs : s.nonempty) : 0 / s = 0 :=
s.zero_div_subset.antisymm $ by simpa [mem_div] using hs

end group_with_zero

section has_mul
variables [has_mul α] [has_mul β] [mul_hom_class F α β] (m : F) {s t : set α}
include α β

@[to_additive] lemma image_mul : m '' (s * t) = m '' s * m '' t := image_image2_distrib $ map_mul m

@[to_additive]
lemma preimage_mul_preimage_subset {s t : set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
by { rintro _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm ⟩ }

end has_mul

section group
variables [group α] [division_monoid β] [monoid_hom_class F α β] (m : F) {s t : set α}
include α β

@[to_additive] lemma image_div : m '' (s / t) = m '' s / m '' t := image_image2_distrib $ map_div m

@[to_additive]
lemma preimage_div_preimage_subset {s t : set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) :=
by { rintro _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm ⟩ }

end group

@[to_additive]
lemma bdd_above_mul [ordered_comm_monoid α] {A B : set α} :
  bdd_above A → bdd_above B → bdd_above (A * B) :=
begin
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩,
  use bA * bB,
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩,
  exact mul_le_mul' (hbA hxa) (hbB hxb),
end

end set

/-! ### Miscellaneous -/

open set
open_locale pointwise

namespace group

lemma card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : monotone f)
  {B : ℕ} (h2 : ∀ n, f n ≤ B) (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) :
  ∀ k, B ≤ k → f k = f B :=
begin
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1),
  { contrapose! h2,
    suffices : ∀ n : ℕ, n ≤ B + 1 → n ≤ f n,
    { exact ⟨B + 1, this (B + 1) (le_refl (B + 1))⟩ },
    exact λ n, nat.rec (λ h, nat.zero_le (f 0)) (λ n ih h, lt_of_le_of_lt (ih (n.le_succ.trans h))
      (lt_of_le_of_ne (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h)))) n },
  { obtain ⟨n, hn1, hn2⟩ := key,
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n :=
    λ k, nat.rec ⟨hn2, rfl⟩ (λ k ih, ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k,
    replace key : ∀ k : ℕ, n ≤ k → f k = f n :=
    λ k hk, (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2,
    exact λ k hk, (key k (hn1.trans hk)).trans (key B hn1).symm },
end

end group
