/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.module.basic
import data.set.finite
import group_theory.submonoid.basic

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`.

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
`has_scalar α β → has_scalar α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_scalar_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
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

@[to_additive] lemma finite.inv (hs : finite s) : finite s⁻¹ :=
hs.preimage $ inv_injective.inj_on _

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

open mul_opposite

@[to_additive]
lemma image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by simp_rw [←image_inv, image_comm op_inv]

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

@[to_additive] lemma finite.mul : finite s → finite t → finite (s * t) := finite.image2 _

/-- Multiplication preserves finiteness. -/
@[to_additive "Addition preserves finiteness."]
def fintype_mul [decidable_eq α] (s t : set α) [fintype s] [fintype t] : fintype (s * t : set α) :=
set.fintype_image2 _ _ _

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
protected def has_nsmul [has_zero α] [has_add α] : has_scalar ℕ (set α) := ⟨nsmul_rec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def has_npow [has_one α] [has_mul α] : has_pow (set α) ℕ := ⟨λ s n, npow_rec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def has_zsmul [has_zero α] [has_add α] [has_neg α] : has_scalar ℤ (set α) := ⟨zsmul_rec⟩

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
variables [monoid α] {s t : set α} {a : α}

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

@[to_additive] lemma empty_pow (n : ℕ) (hn : n ≠ 0) : (∅ : set α) ^ n = ∅ :=
by rw [← tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, empty_mul]

@[to_additive]
instance decidable_mem_mul [fintype α] [decidable_eq α] [decidable_pred (∈ s)]
  [decidable_pred (∈ t)] :
  decidable_pred (∈ s * t) :=
λ _, decidable_of_iff _ mem_mul.symm

@[to_additive]
instance decidable_mem_pow [fintype α] [decidable_eq α] [decidable_pred (∈ s)] (n : ℕ) :
  decidable_pred (∈ (s ^ n)) :=
begin
  induction n with n ih,
  { simp_rw [pow_zero, mem_one], apply_instance },
  { letI := ih, rw pow_succ, apply_instance }
end

@[simp, to_additive] lemma univ_mul_univ : (univ : set α) * univ = univ :=
begin
  have : ∀ x, ∃ a b : α, a * b = x := λ x, ⟨x, 1, mul_one x⟩,
  simpa only [mem_mul, eq_univ_iff_forall, mem_univ, true_and]
end

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
@[to_additive subtraction_monoid "`set α` is a subtraction monoid under pointwise operations if `α`
is."]
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

section group
variables [group α] {s t : set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/

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

@[to_additive]
lemma bdd_above_mul [ordered_comm_monoid α] {A B : set α} :
  bdd_above A → bdd_above B → bdd_above (A * B) :=
begin
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩,
  use bA * bB,
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩,
  exact mul_le_mul' (hbA hxa) (hbB hxb),
end

open_locale pointwise

section big_operators
open_locale big_operators

variables {ι : Type*} [comm_monoid α]

/-- The n-ary version of `set.mem_mul`. -/
@[to_additive /-" The n-ary version of `set.mem_add`. "-/]
lemma mem_finset_prod (t : finset ι) (f : ι → set α) (a : α) :
  a ∈ ∏ i in t, f i ↔ ∃ (g : ι → α) (hg : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i in t, g i = a :=
begin
  classical,
  induction t using finset.induction_on with i is hi ih generalizing a,
  { simp_rw [finset.prod_empty, set.mem_one],
    exact ⟨λ h, ⟨λ i, a, λ i, false.elim, h.symm⟩, λ ⟨f, _, hf⟩, hf.symm⟩ },
  rw [finset.prod_insert hi, set.mem_mul],
  simp_rw [finset.prod_insert hi],
  simp_rw ih,
  split,
  { rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩,
    refine ⟨function.update g i x, λ j hj, _, _⟩,
    obtain rfl | hj := finset.mem_insert.mp hj,
    { rw function.update_same, exact hx },
    { rw update_noteq (ne_of_mem_of_not_mem hj hi), exact hg hj, },
    rw [finset.prod_update_of_not_mem hi, function.update_same], },
  { rintro ⟨g, hg, rfl⟩,
    exact ⟨g i, is.prod g, hg (is.mem_insert_self _),
      ⟨g, λ i hi, hg (finset.mem_insert_of_mem hi), rfl⟩, rfl⟩ },
end

/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive /-" A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "-/]
lemma mem_fintype_prod [fintype ι] (f : ι → set α) (a : α) :
  a ∈ ∏ i, f i ↔ ∃ (g : ι → α) (hg : ∀ i, g i ∈ f i), ∏ i, g i = a :=
by { rw mem_finset_prod, simp }

/-- The n-ary version of `set.mul_mem_mul`. -/
@[to_additive /-" The n-ary version of `set.add_mem_add`. "-/]
lemma finset_prod_mem_finset_prod (t : finset ι) (f : ι → set α)
  (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
  ∏ i in t, g i ∈ ∏ i in t, f i :=
by { rw mem_finset_prod, exact ⟨g, hg, rfl⟩ }

/-- The n-ary version of `set.mul_subset_mul`. -/
@[to_additive /-" The n-ary version of `set.add_subset_add`. "-/]
lemma finset_prod_subset_finset_prod (t : finset ι) (f₁ f₂ : ι → set α)
  (hf : ∀ {i}, i ∈ t → f₁ i ⊆ f₂ i) :
  ∏ i in t, f₁ i ⊆ ∏ i in t, f₂ i :=
begin
  intro a,
  rw [mem_finset_prod, mem_finset_prod],
  rintro ⟨g, hg, rfl⟩,
  exact ⟨g, λ i hi, hf hi $ hg hi, rfl⟩
end

@[to_additive]
lemma finset_prod_singleton {M ι : Type*} [comm_monoid M] (s : finset ι) (I : ι → M) :
  ∏ (i : ι) in s, ({I i} : set M) = {∏ (i : ι) in s, I i} :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simpa },
  { intros _ _ H ih,
    rw [finset.prod_insert H, finset.prod_insert H, ih],
    simp }
end

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/

end big_operators

/-! ### Translation/scaling of sets -/

section smul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive has_vadd_set "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in
locale `pointwise`."]
protected def has_scalar_set [has_scalar α β] : has_scalar α (set β) :=
⟨λ a, image (has_scalar.smul a)⟩

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive has_vadd "The pointwise scalar addition of sets `s +ᵥ t` is defined as
`{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def has_scalar [has_scalar α β] : has_scalar (set α) (set β) :=
⟨image2 has_scalar.smul⟩

localized "attribute [instance] set.has_scalar_set set.has_scalar" in pointwise
localized "attribute [instance] set.has_vadd_set set.has_vadd" in pointwise

section has_scalar
variables {ι : Sort*} {κ : ι → Sort*} [has_scalar α β] {s s₁ s₂ : set α} {t t₁ t₂ u : set β} {a : α}
  {b : β}

@[simp, to_additive]
lemma image2_smul : image2 has_scalar.smul s t = s • t := rfl

@[to_additive add_image_prod]
lemma image_smul_prod : (λ x : α × β, x.fst • x.snd) '' s ×ˢ t = s • t := image_prod _

@[to_additive]
lemma mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b := iff.rfl

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image2_of_mem

@[simp, to_additive] lemma empty_smul : (∅ : set α) • t = ∅ := image2_empty_left
@[simp, to_additive] lemma smul_empty : s • (∅ : set β) = ∅ := image2_empty_right
@[simp, to_additive] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp, to_additive] lemma smul_nonempty : (s • t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
@[to_additive] lemma nonempty.smul : s.nonempty → t.nonempty → (s • t).nonempty := nonempty.image2
@[to_additive] lemma nonempty.of_smul_left : (s • t).nonempty → s.nonempty :=
nonempty.of_image2_left
@[to_additive] lemma nonempty.of_smul_right : (s • t).nonempty → t.nonempty :=
nonempty.of_image2_right
@[simp, to_additive] lemma smul_singleton : s • {b} = (• b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_smul : ({a} : set α) • t = a • t := image2_singleton_left
@[simp, to_additive] lemma singleton_smul_singleton : ({a} : set α) • ({b} : set β) = {a • b} :=
image2_singleton

@[to_additive, mono] lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image2_subset
@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image2_subset_left
@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image2_subset_right
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a • b ∈ u := image2_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive] lemma union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image2_union_left
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image2_union_right
@[to_additive] lemma inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image2_inter_subset_left
@[to_additive] lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
image2_inter_subset_right

@[to_additive] lemma Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t := Union_image_left _
@[to_additive] lemma Union_smul_right_image : (⋃ a ∈ t, (• a) '' s) = s • t := Union_image_right _

@[to_additive] lemma Union_smul (s : ι → set α) (t : set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
image2_Union_left _ _ _
@[to_additive] lemma smul_Union (s : set α) (t : ι → set β) : s • (⋃ i, t i) = ⋃ i, s • t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_smul (s : Π i, κ i → set α) (t : set β) : (⋃ i j, s i j) • t = ⋃ i j, s i j • t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma smul_Union₂ (s : set α) (t : Π i, κ i → set β) : s • (⋃ i j, t i j) = ⋃ i j, s • t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_smul_subset (s : ι → set α) (t : set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma smul_Inter_subset (s : set α) (t : ι → set β) : s • (⋂ i, t i) ⊆ ⋂ i, s • t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_smul_subset (s : Π i, κ i → set α) (t : set β) :
  (⋂ i j, s i j) • t ⊆ ⋂ i j, s i j • t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma smul_Inter₂_subset (s : set α) (t : Π i, κ i → set β) :
  s • (⋂ i j, t i j) ⊆ ⋂ i j, s • t i j :=
image2_Inter₂_subset_right _ _ _

@[to_additive] lemma finite.smul : finite s → finite t → finite (s • t) := finite.image2 _

end has_scalar

section has_scalar_set
variables {ι : Sort*} {κ : ι → Sort*} [has_scalar α β] {s t t₁ t₂ : set β} {a : α} {b : β} {x y : β}

@[simp, to_additive] lemma image_smul : (λ x, a • x) '' t = a • t := rfl

@[to_additive] lemma mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := iff.rfl

@[to_additive] lemma smul_mem_smul_set : b ∈ s → a • b ∈ a • s := mem_image_of_mem _

@[simp, to_additive] lemma smul_set_empty : a • (∅ : set β) = ∅ := image_empty _
@[simp, to_additive] lemma smul_set_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty
@[simp, to_additive] lemma smul_set_nonempty : (a • s).nonempty ↔ s.nonempty := nonempty_image_iff

@[simp, to_additive] lemma smul_set_singleton : a • ({b} : set β) = {a • b} := image_singleton

@[to_additive] lemma smul_set_mono (h : s ⊆ t) : a • s ⊆ a • t := image_subset _ h

@[to_additive] lemma smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ := image_union _ _ _

@[to_additive]
lemma smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ (a • t₂) := image_inter_subset _ _ _

@[to_additive]
lemma smul_set_Union (a : α) (s : ι → set β) : a • (⋃ i, s i) = ⋃ i, a • s i := image_Union

@[to_additive]
lemma smul_set_Union₂ (a : α) (s : Π i, κ i → set β) : a • (⋃ i j, s i j) = ⋃ i j, a • s i j :=
image_Union₂ _ _

@[to_additive]
lemma smul_set_Inter_subset (a : α) (t : ι → set β) : a • (⋂ i, t i) ⊆ ⋂ i, a • t i :=
image_Inter_subset _ _

@[to_additive]
lemma smul_set_Inter₂_subset (a : α) (t : Π i, κ i → set β) :
  a • (⋂ i j, t i j) ⊆ ⋂ i j, a • t i j :=
image_Inter₂_subset _ _

@[to_additive] lemma nonempty.smul_set : s.nonempty → (a • s).nonempty := nonempty.image _
@[to_additive] lemma finite.smul_set : finite s → finite (a • s) := finite.image _

end has_scalar_set

variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

@[to_additive]
lemma smul_set_inter [group α] [mul_action α β] {s t : set β} :
  a • (s ∩ t) = a • s ∩ a • t :=
(image_inter $ mul_action.injective a).symm

lemma smul_set_inter₀ [group_with_zero α] [mul_action α β] {s t : set β} (ha : a ≠ 0) :
  a • (s ∩ t) = a • s ∩ a • t :=
show units.mk0 a ha • _ = _, from smul_set_inter

@[simp, to_additive]
lemma smul_set_univ [group α] [mul_action α β] {a : α} : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[simp, to_additive]
lemma smul_univ [group α] [mul_action α β] {s : set α} (hs : s.nonempty) :
  s • (univ : set β) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩

@[to_additive]
theorem range_smul_range {ι κ : Type*} [has_scalar α β] (b : ι → α) (c : κ → β) :
  range b • range c = range (λ p : ι × κ, b p.1 • c p.2) :=
ext $ λ x, ⟨λ hx, let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := set.mem_smul.1 hx in
  ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
λ ⟨⟨i, j⟩, h⟩, set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[to_additive]
instance smul_comm_class_set [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class α (set β) (set γ) :=
⟨λ _ _ _, image_image2_distrib_right $ smul_comm _⟩

@[to_additive]
instance smul_comm_class_set' [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) β (set γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) (set β) (set γ) :=
⟨λ _ _ _, image2_left_comm smul_comm⟩

instance is_scalar_tower [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower α β (set γ) :=
{ smul_assoc := λ a b T, by simp only [←image_smul, image_image, smul_assoc] }

instance is_scalar_tower' [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower α (set β) (set γ) :=
⟨λ _ _ _, image2_image_left_comm $ smul_assoc _⟩

instance is_scalar_tower'' [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower (set α) (set β) (set γ) :=
{ smul_assoc := λ T T' T'', image2_assoc smul_assoc }

instance is_central_scalar [has_scalar α β] [has_scalar αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (set β) :=
⟨λ a S, congr_arg (λ f, f '' S) $ by exact funext (λ _, op_smul_eq_smul _ _)⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `set α`
on `set β`. -/
@[to_additive "An additive action of an additive monoid `α` on a type `β` gives an additive action
of `set α` on `set β`"]
protected def mul_action [monoid α] [mul_action α β] : mul_action (set α) (set β) :=
{ mul_smul := λ _ _ _, image2_assoc mul_smul,
  one_smul := λ s, image2_singleton_left.trans $ by simp_rw [one_smul, image_id'] }

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `set β`. -/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action
on `set β`."]
protected def mul_action_set [monoid α] [mul_action α β] : mul_action α (set β) :=
{ mul_smul := by { intros, simp only [← image_smul, image_image, ← mul_smul] },
  one_smul := by { intros, simp only [← image_smul, one_smul, image_id'] } }

localized "attribute [instance] set.mul_action_set set.add_action_set
  set.mul_action set.add_action" in pointwise

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `set β`. -/
protected def distrib_mul_action_set [monoid α] [add_monoid β] [distrib_mul_action α β] :
  distrib_mul_action α (set β) :=
{ smul_add := λ _ _ _, image_image2_distrib $ smul_add _,
  smul_zero := λ _, image_singleton.trans $ by rw [smul_zero, singleton_zero] }

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mul_distrib_mul_action_set [monoid α] [monoid β] [mul_distrib_mul_action α β] :
  mul_distrib_mul_action α (set β) :=
{ smul_mul := λ _ _ _, image_image2_distrib $ smul_mul' _,
  smul_one := λ _, image_singleton.trans $ by rw [smul_one, singleton_one] }

localized "attribute [instance] set.distrib_mul_action_set set.mul_distrib_mul_action_set"
  in pointwise

end smul

section vsub
variables {ι : Sort*} {κ : ι → Sort*} [has_vsub α β] {s s₁ s₂ t t₁ t₂ : set β} {u : set α} {a : α}
  {b c : β}
include α

instance has_vsub : has_vsub (set α) (set β) := ⟨image2 (-ᵥ)⟩

@[simp] lemma image2_vsub : (image2 has_vsub.vsub s t : set α) = s -ᵥ t := rfl

lemma image_vsub_prod : (λ x : β × β, x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t := image_prod _

lemma mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a := iff.rfl

lemma vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t := mem_image2_of_mem hb hc

@[simp] lemma empty_vsub (t : set β) : ∅ -ᵥ t = ∅ := image2_empty_left
@[simp] lemma vsub_empty (s : set β) : s -ᵥ ∅ = ∅ := image2_empty_right
@[simp] lemma vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp] lemma vsub_nonempty : (s -ᵥ t : set α).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
lemma nonempty.vsub : s.nonempty → t.nonempty → (s -ᵥ t : set α).nonempty := nonempty.image2
lemma nonempty.of_vsub_left : (s -ᵥ t :set α).nonempty → s.nonempty := nonempty.of_image2_left
lemma nonempty.of_vsub_right : (s -ᵥ t : set α).nonempty → t.nonempty := nonempty.of_image2_right
@[simp] lemma vsub_singleton (s : set β) (b : β) : s -ᵥ {b} = (-ᵥ b) '' s := image2_singleton_right
@[simp] lemma singleton_vsub (t : set β) (b : β) : {b} -ᵥ t = ((-ᵥ) b) '' t := image2_singleton_left
@[simp] lemma singleton_vsub_singleton : ({b} : set β) -ᵥ {c} = {b -ᵥ c} := image2_singleton

@[mono] lemma vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ := image2_subset
lemma vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ := image2_subset_left
lemma vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t := image2_subset_right
lemma vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x -ᵥ y ∈ u := image2_subset_iff
lemma vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t := vsub_subset_vsub h h

lemma union_vsub : (s₁ ∪ s₂) -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) := image2_union_left
lemma vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) := image2_union_right
lemma inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) := image2_inter_subset_left
lemma vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) := image2_inter_subset_right

lemma Union_vsub_left_image : (⋃ a ∈ s, ((-ᵥ) a) '' t) = s -ᵥ t := Union_image_left _
lemma Union_vsub_right_image : (⋃ a ∈ t, (-ᵥ a) '' s) = s -ᵥ t := Union_image_right _

lemma Union_vsub (s : ι → set β) (t : set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
image2_Union_left _ _ _
lemma vsub_Union (s : set β) (t : ι → set β) : s -ᵥ (⋃ i, t i) = ⋃ i, s -ᵥ t i :=
image2_Union_right _ _ _

lemma Union₂_vsub (s : Π i, κ i → set β) (t : set β) : (⋃ i j, s i j) -ᵥ t = ⋃ i j, s i j -ᵥ t :=
image2_Union₂_left _ _ _

lemma vsub_Union₂ (s : set β) (t : Π i, κ i → set β) : s -ᵥ (⋃ i j, t i j) = ⋃ i j, s -ᵥ t i j :=
image2_Union₂_right _ _ _

lemma Inter_vsub_subset (s : ι → set β) (t : set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
image2_Inter_subset_left _ _ _

lemma vsub_Inter_subset (s : set β) (t : ι → set β) : s -ᵥ (⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
image2_Inter_subset_right _ _ _

lemma Inter₂_vsub_subset (s : Π i, κ i → set β) (t : set β) :
  (⋂ i j, s i j) -ᵥ t ⊆ ⋂ i j, s i j -ᵥ t :=
image2_Inter₂_subset_left _ _ _

lemma vsub_Inter₂_subset (s : set β) (t : Π i, κ i → set β) :
  s -ᵥ (⋂ i j, t i j) ⊆ ⋂ i j, s -ᵥ t i j :=
image2_Inter₂_subset_right _ _ _

lemma finite.vsub (hs : finite s) (ht : finite t) : finite (s -ᵥ t) := hs.image2 _ ht

end vsub

open_locale pointwise

section ring
variables [ring α] [add_comm_group β] [module α β] {s : set α} {t : set β} {a : α}

@[simp] lemma neg_smul_set : -a • t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, neg_smul]

@[simp] lemma smul_set_neg : a • -t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, smul_neg]

@[simp] protected lemma neg_smul : -s • t = -(s • t) :=
by { simp_rw ←image_neg, exact image2_image_left_comm neg_smul }

@[simp] protected lemma smul_neg : s • -t = -(s • t) :=
by { simp_rw ←image_neg, exact image_image2_right_comm smul_neg }

end ring

section mul_hom

variables [has_mul α] [has_mul β] [mul_hom_class F α β] (m : F) {s t : set α}

@[to_additive]
lemma image_mul : (m : α → β) '' (s * t) = m '' s * m '' t := image_image2_distrib $ map_mul m

@[to_additive]
lemma preimage_mul_preimage_subset {s t : set β} : (m : α → β) ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
by { rintro _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm ⟩ }

end mul_hom

end set

open set
open_locale pointwise

section

section smul_with_zero
variables [has_zero α] [has_zero β] [smul_with_zero α β]

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
lemma zero_smul_set {s : set β} (h : s.nonempty) : (0 : α) • s = (0 : set β) :=
by simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

lemma zero_smul_subset (s : set β) : (0 : α) • s ⊆ 0 := image_subset_iff.2 $ λ x _, zero_smul α x

lemma subsingleton_zero_smul_set (s : set β) : ((0 : α) • s).subsingleton :=
subsingleton_singleton.mono (zero_smul_subset s)

lemma zero_mem_smul_set {t : set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
⟨0, h, smul_zero' _ _⟩

variables [no_zero_smul_divisors α β] {s : set α} {t : set β} {a : α}

lemma zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.nonempty ∨ (0 : β) ∈ t ∧ s.nonempty :=
begin
  split,
  { rintro ⟨a, b, ha, hb, h⟩,
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h,
    { exact or.inl ⟨ha, b, hb⟩ },
    { exact or.inr ⟨hb, a, ha⟩ } },
  { rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩),
    { exact ⟨0, b, hs, hb, zero_smul _ _⟩ },
    { exact ⟨a, 0, ha, ht, smul_zero' _ _⟩ } }
end

lemma zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
begin
  refine ⟨_, zero_mem_smul_set⟩,
  rintro ⟨b, hb, h⟩,
  rwa (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha at hb,
end

end smul_with_zero

lemma smul_add_set [monoid α] [add_monoid β] [distrib_mul_action α β] (c : α) (s t : set β) :
  c • (s + t) = c • s + c • t :=
image_add (distrib_mul_action.to_add_monoid_hom β c).to_add_hom

section group
variables [group α] [mul_action α β] {A B : set β} {a : α} {x : β}

@[simp, to_additive]
lemma smul_mem_smul_set_iff : a • x ∈ a • A ↔ x ∈ A :=
⟨λ h, begin
  rw [←inv_smul_smul a x, ←inv_smul_smul a A],
  exact smul_mem_smul_set h,
end, smul_mem_smul_set⟩

@[to_additive]
lemma mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show x ∈ mul_action.to_perm a '' A ↔ _, from mem_image_equiv

@[to_additive]
lemma mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
by simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive]
lemma preimage_smul (a : α) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
((mul_action.to_perm a).symm.image_eq_preimage _).symm

@[to_additive]
lemma preimage_smul_inv (a : α) (t : set β) : (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul (to_units a)⁻¹ t

@[simp, to_additive]
lemma set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
image_subset_image_iff $ mul_action.injective _

@[to_additive]
lemma set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
(image_subset_iff).trans $ iff_of_eq $ congr_arg _ $
  preimage_equiv_eq_image_symm _ $ mul_action.to_perm _

@[to_additive]
lemma subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
iff.symm $ (image_subset_iff).trans $ iff.symm $ iff_of_eq $ congr_arg _ $
  image_equiv_eq_preimage_symm _ $ mul_action.to_perm _

end group

section group_with_zero
variables [group_with_zero α] [mul_action α β] {s : set α} {a : α}

@[simp] lemma smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : set β)
  (x : β) : a • x ∈ a • A ↔ x ∈ A :=
show units.mk0 a ha • _ ∈ _ ↔ _, from smul_mem_smul_set_iff

lemma mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : set β) (x : β) :
  x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show _ ∈ units.mk0 a ha • _ ↔ _, from mem_smul_set_iff_inv_smul_mem

lemma mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
show _ ∈ (units.mk0 a ha)⁻¹ • _ ↔ _, from mem_inv_smul_set_iff

lemma preimage_smul₀ (ha : a ≠ 0) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
preimage_smul (units.mk0 a ha) t

lemma preimage_smul_inv₀ (ha : a ≠ 0) (t : set β) :
  (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul ((units.mk0 a ha)⁻¹) t

@[simp] lemma set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} :
  a • A ⊆ a • B ↔ A ⊆ B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_set_smul_iff

lemma set_smul_subset_iff₀ (ha : a ≠ 0) {A B : set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_iff

lemma subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
show _ ⊆ units.mk0 a ha • _ ↔ _, from subset_set_smul_iff

lemma smul_univ₀ (hs : ¬ s ⊆ 0) : s • (univ : set β) = univ :=
let ⟨a, ha, ha₀⟩ := not_subset.1 hs in eq_univ_of_forall $ λ b,
  ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩

lemma smul_set_univ₀ (ha : a ≠ 0) : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul₀ ha _⟩

end group_with_zero

end

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/
namespace submonoid

variables {M : Type*} [monoid M] {s t u : set M}

@[to_additive]
lemma mul_subset {S : submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S :=
by { rintro _ ⟨p, q, hp, hq, rfl⟩, exact submonoid.mul_mem _ (hs hp) (ht hq) }

@[to_additive]
lemma mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ submonoid.closure u :=
mul_subset (subset.trans hs submonoid.subset_closure) (subset.trans ht submonoid.subset_closure)

@[to_additive]
lemma coe_mul_self_eq (s : submonoid M) : (s : set M) * s = s :=
begin
  ext x,
  refine ⟨_, λ h, ⟨x, 1, h, s.one_mem, mul_one x⟩⟩,
  rintro ⟨a, b, ha, hb, rfl⟩,
  exact s.mul_mem ha hb
end

@[to_additive]
lemma closure_mul_le (S T : set M) : closure (S * T) ≤ closure S ⊔ closure T :=
Inf_le $ λ x ⟨s, t, hs, ht, hx⟩, hx ▸ (closure S ⊔ closure T).mul_mem
    (set_like.le_def.mp le_sup_left $ subset_closure hs)
    (set_like.le_def.mp le_sup_right $ subset_closure ht)

@[to_additive]
lemma sup_eq_closure (H K : submonoid M) : H ⊔ K = closure (H * K) :=
le_antisymm
  (sup_le
    (λ h hh, subset_closure ⟨h, 1, hh, K.one_mem, mul_one h⟩)
    (λ k hk, subset_closure ⟨1, k, H.one_mem, hk, one_mul k⟩))
  (by conv_rhs { rw [← closure_eq H, ← closure_eq K] }; apply closure_mul_le)

lemma pow_smul_mem_closure_smul {N : Type*} [comm_monoid N] [mul_action M N]
  [is_scalar_tower M N N] (r : M) (s : set N) {x : N} (hx : x ∈ closure s) :
  ∃ n : ℕ, r ^ n • x ∈ closure (r • s) :=
begin
  apply @closure_induction N _ s
    (λ (x : N), ∃ n : ℕ, r ^ n • x ∈ closure (r • s)) _ hx,
  { intros x hx,
    exact ⟨1, subset_closure ⟨_, hx, by rw pow_one⟩⟩ },
  { exact ⟨0, by simpa using one_mem _⟩ },
  { rintro x y ⟨nx, hx⟩ ⟨ny, hy⟩,
    use nx + ny,
    convert mul_mem hx hy,
    rw [pow_add, smul_mul_assoc, mul_smul, mul_comm, ← smul_mul_assoc, mul_comm] }
end

end submonoid

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

variables {G : Type*} [group G] [fintype G] (S : set G)

@[to_additive]
lemma card_pow_eq_card_pow_card_univ [∀ (k : ℕ), decidable_pred (∈ (S ^ k))] :
  ∀ k, fintype.card G ≤ k → fintype.card ↥(S ^ k) = fintype.card ↥(S ^ (fintype.card G)) :=
begin
  have hG : 0 < fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩,
  by_cases hS : S = ∅,
  { refine λ k hk, fintype.card_congr _,
    rw [hS, empty_pow _ (ne_of_gt (lt_of_lt_of_le hG hk)), empty_pow _ (ne_of_gt hG)] },
  obtain ⟨a, ha⟩ := set.ne_empty_iff_nonempty.mp hS,
  classical!,
  have key : ∀ a (s t : set G), (∀ b : G, b ∈ s → a * b ∈ t) → fintype.card s ≤ fintype.card t,
  { refine λ a s t h, fintype.card_le_of_injective (λ ⟨b, hb⟩, ⟨a * b, h b hb⟩) _,
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc,
    exact subtype.ext (mul_left_cancel (subtype.ext_iff.mp hbc)) },
  have mono : monotone (λ n, fintype.card ↥(S ^ n) : ℕ → ℕ) :=
  monotone_nat_of_le_succ (λ n, key a _ _ (λ b hb, set.mul_mem_mul ha hb)),
  convert card_pow_eq_card_pow_card_univ_aux mono (λ n, set_fintype_card_le_univ (S ^ n))
    (λ n h, le_antisymm (mono (n + 1).le_succ) (key a⁻¹ _ _ _)),
  { simp only [finset.filter_congr_decidable, fintype.card_of_finset] },
  replace h : {a} * S ^ n = S ^ (n + 1),
  { refine set.eq_of_subset_of_card_le _ (le_trans (ge_of_eq h) _),
    { exact mul_subset_mul (set.singleton_subset_iff.mpr ha) set.subset.rfl },
    { convert key a (S ^ n) ({a} * S ^ n) (λ b hb, set.mul_mem_mul (set.mem_singleton a) hb) } },
  rw [pow_succ', ←h, mul_assoc, ←pow_succ', h],
  rintro _ ⟨b, c, hb, hc, rfl⟩,
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_left],
end

end group
