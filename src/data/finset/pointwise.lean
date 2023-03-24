/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import data.finset.n_ary
import data.finset.preimage
import data.set.pointwise.smul
import data.set.pointwise.list_of_fn

/-!
# Pointwise operations of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:
* `0` (`finset.has_zero`): The singleton `{0}`.
* `1` (`finset.has_one`): The singleton `{1}`.
* `-s` (`finset.has_neg`): Negation, finset of all `-x` where `x ∈ s`.
* `s⁻¹` (`finset.has_inv`): Inversion, finset of all `x⁻¹` where `x ∈ s`.
* `s + t` (`finset.has_add`): Addition, finset of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s * t` (`finset.has_mul`): Multiplication, finset of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s - t` (`finset.has_sub`): Subtraction, finset of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s / t` (`finset.has_div`): Division, finset of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t` (`finset.has_vadd`): Scalar addition, finset of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s • t` (`finset.has_smul`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`finset.has_vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`finset.has_smul_finset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`finset.has_vadd_finset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the locale `pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

open function
open_locale big_operators pointwise

variables {F α β γ : Type*}

namespace finset

/-! ### `0`/`1` as finsets -/

section has_one
variables [has_one α] {s : finset α} {a : α}

/-- The finset `1 : finset α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The finset `0 : finset α` is defined as `{0}` in locale `pointwise`."]
protected def has_one : has_one (finset α) := ⟨{1}⟩

localized "attribute [instance] finset.has_one finset.has_zero" in pointwise

@[simp, to_additive] lemma mem_one : a ∈ (1 : finset α) ↔ a = 1 := mem_singleton
@[simp, norm_cast, to_additive] lemma coe_one : ↑(1 : finset α) = (1 : set α) := coe_singleton 1
@[simp, to_additive] lemma one_subset : (1 : finset α) ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff
@[to_additive] lemma singleton_one : ({1} : finset α) = 1 := rfl
@[to_additive] lemma one_mem_one : (1 : α) ∈ (1 : finset α) := mem_singleton_self _
@[to_additive] lemma one_nonempty : (1 : finset α).nonempty := ⟨1, one_mem_one⟩
@[simp, to_additive] protected lemma map_one {f : α ↪ β} : map f 1 = {f 1} := map_singleton f 1
@[simp, to_additive] lemma image_one [decidable_eq β] {f : α → β} : image f 1 = {f 1} :=
image_singleton _ _
@[to_additive] lemma subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 := subset_singleton_iff
@[to_additive] lemma nonempty.subset_one_iff (h : s.nonempty) : s ⊆ 1 ↔ s = 1 :=
h.subset_singleton_iff

/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singleton_one_hom : one_hom α (finset α) := ⟨singleton, singleton_one⟩

@[simp, to_additive] lemma coe_singleton_one_hom : (singleton_one_hom : α → finset α) = singleton :=
rfl
@[simp, to_additive] lemma singleton_one_hom_apply (a : α) : singleton_one_hom a = {a} := rfl

/-- Lift a `one_hom` to `finset` via `image`. -/
@[to_additive "Lift a `zero_hom` to `finset` via `image`", simps]
def image_one_hom [decidable_eq β] [has_one β] [one_hom_class F α β] (f : F) :
  one_hom (finset α) (finset β) :=
{ to_fun := finset.image f,
  map_one' := by rw [image_one, map_one, singleton_one] }

end has_one

/-! ### Finset negation/inversion -/

section has_inv
variables [decidable_eq α] [has_inv α] {s s₁ s₂ t t₁ t₂ u : finset α} {a b : α}

/-- The pointwise inversion of finset `s⁻¹` is defined as `{x⁻¹ | x ∈ s}` in locale `pointwise`. -/
@[to_additive "The pointwise negation of finset `-s` is defined as `{-x | x ∈ s}` in locale
`pointwise`."]
protected def has_inv : has_inv (finset α) := ⟨image has_inv.inv⟩

localized "attribute [instance] finset.has_inv finset.has_neg" in pointwise

@[to_additive] lemma inv_def : s⁻¹ = s.image (λ x, x⁻¹) := rfl
@[to_additive] lemma image_inv : s.image (λ x, x⁻¹)  = s⁻¹ := rfl
@[to_additive] lemma mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x := mem_image
@[to_additive] lemma inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ := mem_image_of_mem _ ha
@[to_additive] lemma card_inv_le : s⁻¹.card ≤ s.card := card_image_le

@[simp, to_additive] lemma inv_empty : (∅ : finset α)⁻¹ = ∅ := image_empty _
@[simp, to_additive] lemma inv_nonempty_iff : s⁻¹.nonempty ↔ s.nonempty := nonempty.image_iff _

alias inv_nonempty_iff ↔ nonempty.inv nonempty.of_inv

@[to_additive, mono] lemma inv_subset_inv  (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ := image_subset_image h

attribute [mono] neg_subset_neg

@[simp, to_additive] lemma inv_singleton (a : α) : ({a} : finset α)⁻¹ = {a⁻¹} := image_singleton _ _

@[simp, to_additive]
lemma inv_insert (a : α) (s : finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := image_insert _ _ _

end has_inv

open_locale pointwise

section has_involutive_inv
variables [decidable_eq α] [has_involutive_inv α] (s : finset α)

@[simp, norm_cast, to_additive]
lemma coe_inv : ↑(s⁻¹) = (s : set α)⁻¹ := coe_image.trans set.image_inv

@[simp, to_additive] lemma card_inv : s⁻¹.card = s.card := card_image_of_injective _ inv_injective

@[simp, to_additive] lemma preimage_inv : s.preimage has_inv.inv (inv_injective.inj_on _) = s⁻¹ :=
coe_injective $ by rw [coe_preimage, set.inv_preimage, coe_inv]

end has_involutive_inv

/-! ### Finset addition/multiplication -/

section has_mul
variables [decidable_eq α] [decidable_eq β] [has_mul α] [has_mul β] [mul_hom_class F α β] (f : F)
  {s s₁ s₂ t t₁ t₂ u : finset α} {a b : α}

/-- The pointwise multiplication of finsets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}`
in locale `pointwise`. -/
@[to_additive "The pointwise addition of finsets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in
locale `pointwise`."]
protected def has_mul : has_mul (finset α) := ⟨image₂ (*)⟩

localized "attribute [instance] finset.has_mul finset.has_add" in pointwise

@[to_additive]
lemma mul_def : s * t = (s ×ˢ t).image (λ p : α × α, p.1 * p.2) := rfl

@[to_additive]
lemma image_mul_product : (s ×ˢ t).image (λ x : α × α, x.fst * x.snd) = s * t := rfl

@[to_additive]
lemma mem_mul {x : α} : x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x := mem_image₂

@[simp, norm_cast, to_additive]
lemma coe_mul (s t : finset α) : (↑(s * t) : set α) = ↑s * ↑t := coe_image₂ _ _ _

@[to_additive] lemma mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t := mem_image₂_of_mem
@[to_additive] lemma card_mul_le : (s * t).card ≤ s.card * t.card := card_image₂_le _ _ _

@[to_additive] lemma card_mul_iff :
  (s * t).card = s.card * t.card ↔
    (s ×ˢ t : set (α × α)).inj_on (λ p, p.1 * p.2) := card_image₂_iff

@[simp, to_additive] lemma empty_mul (s : finset α) : ∅ * s = ∅ := image₂_empty_left
@[simp, to_additive] lemma mul_empty (s : finset α) : s * ∅ = ∅ := image₂_empty_right
@[simp, to_additive] lemma mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff
@[simp, to_additive] lemma mul_nonempty : (s * t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image₂_nonempty_iff
@[to_additive] lemma nonempty.mul : s.nonempty → t.nonempty → (s * t).nonempty := nonempty.image₂
@[to_additive] lemma nonempty.of_mul_left : (s * t).nonempty → s.nonempty := nonempty.of_image₂_left
@[to_additive] lemma nonempty.of_mul_right : (s * t).nonempty → t.nonempty :=
nonempty.of_image₂_right
@[to_additive] lemma mul_singleton (a : α) : s * {a} = s.image (* a) := image₂_singleton_right
@[to_additive] lemma singleton_mul (a : α) : {a} * s = s.image ((*) a) := image₂_singleton_left
@[simp, to_additive] lemma singleton_mul_singleton (a b : α) : ({a} : finset α) * {b} = {a * b} :=
image₂_singleton

@[to_additive, mono] lemma mul_subset_mul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ * t₁ ⊆ s₂ * t₂ := image₂_subset
@[to_additive] lemma mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ := image₂_subset_left
@[to_additive] lemma mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t := image₂_subset_right
@[to_additive] lemma mul_subset_iff : s * t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x * y ∈ u := image₂_subset_iff

attribute [mono] add_subset_add

@[to_additive] lemma union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t := image₂_union_left
@[to_additive] lemma mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ := image₂_union_right
@[to_additive] lemma inter_mul_subset : (s₁ ∩ s₂) * t ⊆ s₁ * t ∩ (s₂ * t) :=
image₂_inter_subset_left
@[to_additive] lemma mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
image₂_inter_subset_right

/-- If a finset `u` is contained in the product of two sets `s * t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' * t'`. -/
@[to_additive "If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`."]
lemma subset_mul {s t : set α} : ↑u ⊆ s * t → ∃ s' t' : finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' * t' :=
subset_image₂

@[to_additive] lemma image_mul : (s * t).image (f : α → β) = s.image f * t.image f :=
image_image₂_distrib $ map_mul f

/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singleton_mul_hom : α →ₙ* finset α := ⟨singleton, λ a b, (singleton_mul_singleton _ _).symm⟩

@[simp, to_additive] lemma coe_singleton_mul_hom : (singleton_mul_hom : α → finset α) = singleton :=
rfl
@[simp, to_additive] lemma singleton_mul_hom_apply (a : α) : singleton_mul_hom a = {a} := rfl

/-- Lift a `mul_hom` to `finset` via `image`. -/
@[to_additive "Lift an `add_hom` to `finset` via `image`", simps]
def image_mul_hom : finset α →ₙ* finset β :=
{ to_fun := finset.image f,
  map_mul' := λ s t, image_mul _ }

end has_mul

/-! ### Finset subtraction/division -/

section has_div
variables [decidable_eq α] [has_div α] {s s₁ s₂ t t₁ t₂ u : finset α} {a b : α}

/-- The pointwise division of sfinets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive "The pointwise subtraction of finsets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}`
in locale `pointwise`."]
protected def has_div : has_div (finset α) := ⟨image₂ (/)⟩

localized "attribute [instance] finset.has_div finset.has_sub" in pointwise

@[to_additive]
lemma div_def : s / t = (s ×ˢ t).image (λ p : α × α, p.1 / p.2) := rfl

@[to_additive add_image_prod]
lemma image_div_prod : (s ×ˢ t).image (λ x : α × α, x.fst / x.snd)  = s / t := rfl

@[to_additive] lemma mem_div : a ∈ s / t ↔ ∃ b c, b ∈ s ∧ c ∈ t ∧ b / c = a := mem_image₂

@[simp, norm_cast, to_additive]
lemma coe_div (s t : finset α) : (↑(s / t) : set α) = ↑s / ↑t := coe_image₂ _ _ _

@[to_additive] lemma div_mem_div : a ∈ s → b ∈ t →  a / b ∈ s / t := mem_image₂_of_mem
@[to_additive] lemma div_card_le : (s / t).card ≤ s.card * t.card := card_image₂_le _ _ _

@[simp, to_additive] lemma empty_div (s : finset α) : ∅ / s = ∅ := image₂_empty_left
@[simp, to_additive] lemma div_empty (s : finset α) : s / ∅ = ∅ := image₂_empty_right
@[simp, to_additive] lemma div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff
@[simp, to_additive] lemma div_nonempty : (s / t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image₂_nonempty_iff
@[to_additive] lemma nonempty.div : s.nonempty → t.nonempty → (s / t).nonempty := nonempty.image₂
@[to_additive] lemma nonempty.of_div_left : (s / t).nonempty → s.nonempty := nonempty.of_image₂_left
@[to_additive] lemma nonempty.of_div_right : (s / t).nonempty → t.nonempty :=
nonempty.of_image₂_right
@[simp, to_additive] lemma div_singleton (a : α) : s / {a} = s.image (/ a) := image₂_singleton_right
@[simp, to_additive] lemma singleton_div (a : α) : {a} / s = s.image ((/) a) :=
image₂_singleton_left
@[simp, to_additive] lemma singleton_div_singleton (a b : α) : ({a} : finset α) / {b} = {a / b} :=
image₂_singleton

@[to_additive, mono] lemma div_subset_div : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ / t₁ ⊆ s₂ / t₂ := image₂_subset
@[to_additive] lemma div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ := image₂_subset_left
@[to_additive] lemma div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t := image₂_subset_right
@[to_additive] lemma div_subset_iff : s / t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x / y ∈ u := image₂_subset_iff

attribute [mono] sub_subset_sub

@[to_additive] lemma union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t := image₂_union_left
@[to_additive] lemma div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ := image₂_union_right
@[to_additive] lemma inter_div_subset : (s₁ ∩ s₂) / t ⊆ s₁ / t ∩ (s₂ / t) :=
image₂_inter_subset_left
@[to_additive] lemma div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
image₂_inter_subset_right

/-- If a finset `u` is contained in the product of two sets `s / t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' / t'`. -/
@[to_additive "If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`."]
lemma subset_div {s t : set α} : ↑u ⊆ s / t → ∃ s' t' : finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' / t' :=
subset_image₂

end has_div

/-! ### Instances -/

open_locale pointwise

section instances
variables [decidable_eq α] [decidable_eq β]

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action]. -/
protected def has_nsmul [has_zero α] [has_add α] : has_smul ℕ (finset α) := ⟨nsmul_rec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`finset`. See note [pointwise nat action]. -/
@[to_additive]
protected def has_npow [has_one α] [has_mul α] : has_pow (finset α) ℕ := ⟨λ s n, npow_rec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `finset`. See note [pointwise nat action]. -/
protected def has_zsmul [has_zero α] [has_add α] [has_neg α] : has_smul ℤ (finset α) :=
⟨zsmul_rec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `finset`. See note [pointwise nat action]. -/
@[to_additive] protected def has_zpow [has_one α] [has_mul α] [has_inv α] : has_pow (finset α) ℤ :=
⟨λ s n, zpow_rec n s⟩

localized "attribute [instance] finset.has_nsmul finset.has_npow finset.has_zsmul finset.has_zpow"
  in pointwise

/-- `finset α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_semigroup` under pointwise operations if `α` is. "]
protected def semigroup [semigroup α] : semigroup (finset α) :=
coe_injective.semigroup _ coe_mul

/-- `finset α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_semigroup` under pointwise operations if `α` is. "]
protected def comm_semigroup [comm_semigroup α] : comm_semigroup (finset α) :=
coe_injective.comm_semigroup _ coe_mul

section mul_one_class
variables [mul_one_class α]

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mul_one_class : mul_one_class (finset α) :=
coe_injective.mul_one_class _ (coe_singleton 1) coe_mul

localized "attribute [instance] finset.semigroup finset.add_semigroup finset.comm_semigroup
  finset.add_comm_semigroup finset.mul_one_class finset.add_zero_class" in pointwise

@[to_additive] lemma subset_mul_left (s : finset α) {t : finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t :=
λ a ha, mem_mul.2 ⟨a, 1, ha, ht, mul_one _⟩

@[to_additive] lemma subset_mul_right {s : finset α} (t : finset α) (hs : (1 : α) ∈ s) :
  t ⊆ s * t :=
λ a ha, mem_mul.2 ⟨1, a, hs, ha, one_mul _⟩

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singleton_monoid_hom : α →* finset α := { ..singleton_mul_hom, ..singleton_one_hom }

@[simp, to_additive] lemma coe_singleton_monoid_hom :
  (singleton_monoid_hom : α → finset α) = singleton := rfl
@[simp, to_additive] lemma singleton_monoid_hom_apply (a : α) : singleton_monoid_hom a = {a} := rfl

/-- The coercion from `finset` to `set` as a `monoid_hom`. -/
@[to_additive "The coercion from `finset` to `set` as an `add_monoid_hom`."]
def coe_monoid_hom : finset α →* set α :=
{ to_fun := coe,
  map_one' := coe_one,
  map_mul' := coe_mul }

@[simp, to_additive] lemma coe_coe_monoid_hom : (coe_monoid_hom : finset α → set α) = coe := rfl
@[simp, to_additive] lemma coe_monoid_hom_apply (s : finset α) : coe_monoid_hom s = s := rfl

/-- Lift a `monoid_hom` to `finset` via `image`. -/
@[to_additive "Lift an `add_monoid_hom` to `finset` via `image`", simps]
def image_monoid_hom [mul_one_class β] [monoid_hom_class F α β] (f : F) : finset α →* finset β :=
{ ..image_mul_hom f, ..image_one_hom f }

end mul_one_class

section monoid
variables [monoid α] {s t : finset α} {a : α} {m n : ℕ}

@[simp, norm_cast, to_additive] lemma coe_pow (s : finset α) (n : ℕ) : ↑(s ^ n) = (s ^ n : set α) :=
begin
  change ↑(npow_rec n s) = _,
  induction n with n ih,
  { rw [npow_rec, pow_zero, coe_one] },
  { rw [npow_rec, pow_succ, coe_mul, ih] }
end

/-- `finset α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_monoid` under pointwise operations if `α` is. "]
protected def monoid : monoid (finset α) := coe_injective.monoid _ coe_one coe_mul coe_pow

localized "attribute [instance] finset.monoid finset.add_monoid" in pointwise

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

@[simp, norm_cast, to_additive]
lemma coe_list_prod (s : list (finset α)) : (↑s.prod : set α) = (s.map coe).prod :=
map_list_prod (coe_monoid_hom : finset α →* set α) _

@[to_additive] lemma mem_prod_list_of_fn {a : α} {s : fin n → finset α} :
  a ∈ (list.of_fn s).prod ↔ ∃ f : (Π i : fin n, s i), (list.of_fn (λ i, (f i : α))).prod = a :=
by { rw [←mem_coe, coe_list_prod, list.map_of_fn, set.mem_prod_list_of_fn], refl }

@[to_additive] lemma mem_pow {a : α} {n : ℕ} :
  a ∈ s ^ n ↔ ∃ f : fin n → s, (list.of_fn (λ i, ↑(f i))).prod = a :=
by { simp_rw [←mem_coe, coe_pow, set.mem_pow], refl }

@[simp, to_additive] lemma empty_pow (hn : n ≠ 0) : (∅ : finset α) ^ n = ∅ :=
by rw [←tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, empty_mul]

@[to_additive] lemma mul_univ_of_one_mem [fintype α] (hs : (1 : α) ∈ s) : s * univ = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩

@[to_additive] lemma univ_mul_of_one_mem [fintype α] (ht : (1 : α) ∈ t) : univ * t = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩

@[simp, to_additive] lemma univ_mul_univ [fintype α] : (univ : finset α) * univ = univ :=
mul_univ_of_one_mem $ mem_univ _

@[simp, to_additive nsmul_univ] lemma univ_pow [fintype α] (hn : n ≠ 0) :
  (univ : finset α) ^ n = univ :=
coe_injective $ by rw [coe_pow, coe_univ, set.univ_pow hn]

@[to_additive] protected lemma _root_.is_unit.finset : is_unit a → is_unit ({a} : finset α) :=
is_unit.map (singleton_monoid_hom : α →* finset α)

end monoid

section comm_monoid
variables [comm_monoid α]

/-- `finset α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_monoid` under pointwise operations if `α` is. "]
protected def comm_monoid : comm_monoid (finset α) :=
coe_injective.comm_monoid _ coe_one coe_mul coe_pow

localized "attribute [instance] finset.comm_monoid finset.add_comm_monoid" in pointwise

@[simp, norm_cast, to_additive]
lemma coe_prod {ι : Type*} (s : finset ι) (f : ι → finset α) :
  (↑(∏ i in s, f i) : set α) = ∏ i in s, f i :=
map_prod (coe_monoid_hom : finset α →* set α) _ _

end comm_monoid

open_locale pointwise

section division_monoid
variables [division_monoid α] {s t : finset α}

@[simp, to_additive] lemma coe_zpow (s : finset α) : ∀ n : ℤ, ↑(s ^ n) = (s ^ n : set α)
| (int.of_nat n) := coe_pow _ _
| (int.neg_succ_of_nat n) :=
  by { refine (coe_inv _).trans _, convert congr_arg has_inv.inv (coe_pow _ _) }

@[to_additive] protected lemma mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 :=
by simp_rw [←coe_inj, coe_mul, coe_one, set.mul_eq_one_iff, coe_singleton]

/-- `finset α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`finset α` is a subtraction monoid under pointwise operations if
`α` is."]
protected def division_monoid : division_monoid (finset α) :=
coe_injective.division_monoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[simp, to_additive] lemma is_unit_iff : is_unit s ↔ ∃ a, s = {a} ∧ is_unit a :=
begin
  split,
  { rintro ⟨u, rfl⟩,
    obtain ⟨a, b, ha, hb, h⟩ := finset.mul_eq_one_iff.1 u.mul_inv,
    refine ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩,
    rw [←singleton_mul_singleton, ←ha, ←hb],
    exact u.inv_mul },
  { rintro ⟨a, rfl, ha⟩,
    exact ha.finset }
end

@[simp, to_additive] lemma is_unit_coe : is_unit (s : set α) ↔ is_unit s :=
by simp_rw [is_unit_iff, set.is_unit_iff, coe_eq_singleton]

end division_monoid

/-- `finset α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtraction_comm_monoid "`finset α` is a commutative subtraction monoid under
pointwise operations if `α` is."]
protected def division_comm_monoid [division_comm_monoid α] : division_comm_monoid (finset α) :=
coe_injective.division_comm_monoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

/-- `finset α` has distributive negation if `α` has. -/
protected def has_distrib_neg [has_mul α] [has_distrib_neg α] : has_distrib_neg (finset α) :=
coe_injective.has_distrib_neg _ coe_neg coe_mul

localized "attribute [instance] finset.division_monoid finset.subtraction_monoid
  finset.division_comm_monoid finset.subtraction_comm_monoid finset.has_distrib_neg" in pointwise

section distrib
variables [distrib α] (s t u : finset α)

/-!
Note that `finset α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.

```lean
-- {10, 16, 18, 20, 8, 9}
#eval {1, 2} * ({3, 4} + {5, 6} : finset ℕ)

-- {10, 11, 12, 13, 14, 15, 16, 18, 20, 8, 9}
#eval ({1, 2} : finset ℕ) * {3, 4} + {1, 2} * {5, 6}
```
-/

lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u := image₂_distrib_subset_left mul_add
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u := image₂_distrib_subset_right add_mul

end distrib

section mul_zero_class
variables [mul_zero_class α] {s t : finset α}

/-! Note that `finset` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/

lemma mul_zero_subset (s : finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]
lemma zero_mul_subset (s : finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]

lemma nonempty.mul_zero (hs : s.nonempty) : s * 0 = 0 :=
s.mul_zero_subset.antisymm $ by simpa [mem_mul] using hs

lemma nonempty.zero_mul (hs : s.nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm $ by simpa [mem_mul] using hs

end mul_zero_class

section group
variables [group α] [division_monoid β] [monoid_hom_class F α β] (f : F) {s t : finset α} {a b : α}

/-! Note that `finset` is not a `group` because `s / s ≠ 1` in general. -/

@[simp, to_additive] lemma one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬ disjoint s t :=
by rw [←mem_coe, ←disjoint_coe, coe_div, set.one_mem_div_iff]

@[to_additive] lemma not_one_mem_div_iff : (1 : α) ∉ s / t ↔ disjoint s t :=
one_mem_div_iff.not_left

@[to_additive] lemma nonempty.one_mem_div (h : s.nonempty) : (1 : α) ∈ s / s :=
let ⟨a, ha⟩ := h in mem_div.2 ⟨a, a, ha, ha, div_self' _⟩

@[to_additive] lemma is_unit_singleton (a : α) : is_unit ({a} : finset α) :=
(group.is_unit a).finset

@[simp] lemma is_unit_iff_singleton : is_unit s ↔ ∃ a, s = {a} :=
by simp only [is_unit_iff, group.is_unit, and_true]

@[simp, to_additive]
lemma image_mul_left :
  image (λ b, a * b) t = preimage t (λ b, a⁻¹ * b) ((mul_right_injective _).inj_on _) :=
coe_injective $ by simp

@[simp, to_additive]
lemma image_mul_right : image (* b) t = preimage t (* b⁻¹) ((mul_left_injective _).inj_on _) :=
coe_injective $ by simp

@[to_additive]
lemma image_mul_left' :
  image (λ b, a⁻¹ * b) t = preimage t (λ b, a * b) ((mul_right_injective _).inj_on _) :=
by simp

@[to_additive]
lemma image_mul_right' : image (* b⁻¹) t = preimage t (* b) ((mul_left_injective _).inj_on _) :=
by simp

lemma image_div : (s / t).image (f : α → β) = s.image f / t.image f :=
image_image₂_distrib $ map_div f

end group

section group_with_zero
variables [group_with_zero α] {s t : finset α}

lemma div_zero_subset (s : finset α) : s / 0 ⊆ 0 := by simp [subset_iff, mem_div]
lemma zero_div_subset (s : finset α) : 0 / s ⊆ 0 := by simp [subset_iff, mem_div]

lemma nonempty.div_zero (hs : s.nonempty) : s / 0 = 0 :=
s.div_zero_subset.antisymm $ by simpa [mem_div] using hs

lemma nonempty.zero_div (hs : s.nonempty) : 0 / s = 0 :=
s.zero_div_subset.antisymm $ by simpa [mem_div] using hs

end group_with_zero
end instances

section group
variables [group α] {s t : finset α} {a b : α}

@[simp, to_additive]
lemma preimage_mul_left_singleton :
  preimage {b} ((*) a) ((mul_right_injective _).inj_on _) = {a⁻¹ * b} :=
by { classical, rw [← image_mul_left', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_right_singleton :
  preimage {b} (* a) ((mul_left_injective _).inj_on _) = {b * a⁻¹} :=
by { classical, rw [← image_mul_right', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_left_one : preimage 1 ((*) a) ((mul_right_injective _).inj_on _) = {a⁻¹} :=
by { classical, rw [← image_mul_left', image_one, mul_one] }

@[simp, to_additive]
lemma preimage_mul_right_one : preimage 1 (* b) ((mul_left_injective _).inj_on _) = {b⁻¹} :=
by { classical, rw [← image_mul_right', image_one, one_mul] }

@[to_additive]
lemma preimage_mul_left_one' : preimage 1 ((*) a⁻¹) ((mul_right_injective _).inj_on _) = {a} :=
by rw [preimage_mul_left_one, inv_inv]

@[to_additive]
lemma preimage_mul_right_one' : preimage 1 (* b⁻¹) ((mul_left_injective _).inj_on _) = {b} :=
by rw [preimage_mul_right_one, inv_inv]

end group

/-! ### Scalar addition/multiplication of finsets -/

section has_smul
variables [decidable_eq β] [has_smul α β] {s s₁ s₂ : finset α} {t t₁ t₂ u : finset β} {a : α}
  {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive "The pointwise sum of two finsets `s` and
`t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`."]
protected def has_smul : has_smul (finset α) (finset β) := ⟨image₂ (•)⟩

localized "attribute [instance] finset.has_smul finset.has_vadd" in pointwise

@[to_additive] lemma smul_def : s • t = (s ×ˢ t).image (λ p : α × β, p.1 • p.2) := rfl

@[to_additive]
lemma image_smul_product : (s ×ˢ t).image (λ x : α × β, x.fst • x.snd)  = s • t := rfl

@[to_additive] lemma mem_smul {x : β} : x ∈ s • t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y • z = x := mem_image₂

@[simp, norm_cast, to_additive]
lemma coe_smul (s : finset α) (t : finset β) : (↑(s • t) : set β) = (s : set α) • t :=
coe_image₂ _ _ _

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image₂_of_mem
@[to_additive] lemma smul_card_le : (s • t).card ≤ s.card • t.card := card_image₂_le _ _ _

@[simp, to_additive] lemma empty_smul (t : finset β) : (∅ : finset α) • t = ∅ := image₂_empty_left
@[simp, to_additive] lemma smul_empty (s : finset α) : s • (∅ : finset β) = ∅ := image₂_empty_right
@[simp, to_additive] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff
@[simp, to_additive] lemma smul_nonempty_iff : (s • t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image₂_nonempty_iff
@[to_additive] lemma nonempty.smul : s.nonempty → t.nonempty → (s • t).nonempty := nonempty.image₂
@[to_additive] lemma nonempty.of_smul_left : (s • t).nonempty → s.nonempty :=
nonempty.of_image₂_left
@[to_additive] lemma nonempty.of_smul_right : (s • t).nonempty → t.nonempty :=
nonempty.of_image₂_right
@[to_additive] lemma smul_singleton (b : β) : s • ({b} : finset β) = s.image (• b) :=
image₂_singleton_right
@[to_additive] lemma singleton_smul_singleton (a : α) (b : β) :
  ({a} : finset α) • ({b} : finset β) = {a • b} :=
image₂_singleton

@[to_additive, mono] lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image₂_subset
@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image₂_subset_left
@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image₂_subset_right
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a • b ∈ u := image₂_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive] lemma union_smul [decidable_eq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
image₂_union_left
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image₂_union_right
@[to_additive] lemma inter_smul_subset [decidable_eq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
image₂_inter_subset_left
@[to_additive] lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
image₂_inter_subset_right

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive "If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`."]
lemma subset_smul {s : set α} {t : set β} :
  ↑u ⊆ s • t → ∃ (s' : finset α) (t' : finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
subset_image₂

end has_smul

/-! ### Scalar subtraction of finsets -/

section has_vsub
variables [decidable_eq α] [has_vsub α β] {s s₁ s₂ t t₁ t₂ : finset β} {u : finset α} {a : α}
  {b c : β}
include α

/-- The pointwise product of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
protected def has_vsub : has_vsub (finset α) (finset β) := ⟨image₂ (-ᵥ)⟩

localized "attribute [instance] finset.has_vsub" in pointwise

lemma vsub_def : s -ᵥ t = image₂ (-ᵥ) s t := rfl
@[simp] lemma image_vsub_product : image₂ (-ᵥ) s t  = s -ᵥ t := rfl

lemma mem_vsub : a ∈ s -ᵥ t ↔ ∃ b c, b ∈ s ∧ c ∈ t ∧ b -ᵥ c = a := mem_image₂

@[simp, norm_cast]
lemma coe_vsub (s t : finset β) : (↑(s -ᵥ t) : set α) = (s : set β) -ᵥ t := coe_image₂ _ _ _

lemma vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t := mem_image₂_of_mem
lemma vsub_card_le : (s -ᵥ t : finset α).card ≤ s.card * t.card := card_image₂_le _ _ _

@[simp] lemma empty_vsub (t : finset β) : (∅ : finset β) -ᵥ t = ∅ := image₂_empty_left
@[simp] lemma vsub_empty (s : finset β) : s -ᵥ (∅ : finset β) = ∅ := image₂_empty_right
@[simp] lemma vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff
@[simp] lemma vsub_nonempty : (s -ᵥ t : finset α).nonempty ↔ s.nonempty ∧ t.nonempty :=
image₂_nonempty_iff
lemma nonempty.vsub : s.nonempty → t.nonempty → (s -ᵥ t : finset α).nonempty := nonempty.image₂
lemma nonempty.of_vsub_left : (s -ᵥ t : finset α).nonempty → s.nonempty := nonempty.of_image₂_left
lemma nonempty.of_vsub_right : (s -ᵥ t : finset α).nonempty → t.nonempty := nonempty.of_image₂_right
@[simp] lemma vsub_singleton (b : β) : s -ᵥ ({b} : finset β) = s.image (-ᵥ b) :=
image₂_singleton_right
lemma singleton_vsub (a : β) : ({a} : finset β) -ᵥ t = t.image ((-ᵥ) a) := image₂_singleton_left
@[simp] lemma singleton_vsub_singleton (a b : β) : ({a} : finset β) -ᵥ {b} = {a -ᵥ b} :=
image₂_singleton

@[mono] lemma vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ := image₂_subset
lemma vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ := image₂_subset_left
lemma vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t := image₂_subset_right
lemma vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x -ᵥ y ∈ u := image₂_subset_iff

section
variables [decidable_eq β]

lemma union_vsub : (s₁ ∪ s₂) -ᵥ t = (s₁ -ᵥ t) ∪ (s₂ -ᵥ t) := image₂_union_left
lemma vsub_union : s -ᵥ (t₁ ∪ t₂) = (s -ᵥ t₁) ∪ (s -ᵥ t₂) := image₂_union_right
lemma inter_vsub_subset : (s₁ ∩ s₂) -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) := image₂_inter_subset_left
lemma vsub_inter_subset : s -ᵥ (t₁ ∩ t₂) ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) := image₂_inter_subset_right

end

/-- If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`. -/
lemma subset_vsub {s t : set β} :
  ↑u ⊆ s -ᵥ t → ∃ s' t' : finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' :=
subset_image₂

end has_vsub

open_locale pointwise

/-! ### Translation/scaling of finsets -/

section has_smul
variables [decidable_eq β] [has_smul α β] {s s₁ s₂ t u : finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive "The translation of a finset `s` by a vector `a`:
`a +ᵥ s = {a +ᵥ x | x ∈ s}`."]
protected def has_smul_finset : has_smul α (finset β) := ⟨λ a, image $ (•) a⟩

localized "attribute [instance] finset.has_smul_finset finset.has_vadd_finset" in pointwise

@[to_additive] lemma smul_finset_def : a • s = s.image ((•) a) := rfl
@[to_additive] lemma image_smul : s.image (λ x, a • x)  = a • s := rfl

@[to_additive]
lemma mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x :=
by simp only [finset.smul_finset_def, and.assoc, mem_image, exists_prop, prod.exists, mem_product]

@[simp, norm_cast, to_additive]
lemma coe_smul_finset (a : α) (s : finset β) : (↑(a • s) : set β) = a • s := coe_image

@[to_additive] lemma smul_finset_mem_smul_finset : b ∈ s → a • b ∈ a • s := mem_image_of_mem _
@[to_additive] lemma smul_finset_card_le : (a • s).card ≤ s.card := card_image_le

@[simp, to_additive] lemma smul_finset_empty (a : α) : a • (∅ : finset β) = ∅ := image_empty _
@[simp, to_additive] lemma smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty
@[simp, to_additive] lemma smul_finset_nonempty : (a • s).nonempty ↔ s.nonempty :=
nonempty.image_iff _
@[to_additive] lemma nonempty.smul_finset (hs : s.nonempty) : (a • s).nonempty := hs.image _
@[simp,  to_additive] lemma singleton_smul (a : α) : ({a} : finset α) • t = a • t :=
image₂_singleton_left

@[to_additive, mono]
lemma smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t := image_subset_image

attribute [mono] vadd_finset_subset_vadd_finset

@[simp, to_additive]
lemma smul_finset_singleton (b : β) : a • ({b} : finset β) = {a • b} := image_singleton _ _

@[to_additive] lemma smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ := image_union _ _
@[to_additive] lemma smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ (a • s₂) :=
image_inter_subset _ _ _

@[simp] lemma bUnion_smul_finset (s : finset α) (t : finset β) : s.bUnion (• t) = s • t :=
bUnion_image_left

end has_smul

open_locale pointwise

section instances
variables [decidable_eq γ]

@[to_additive]
instance smul_comm_class_finset [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α β (finset γ) :=
⟨λ _ _, commute.finset_image $ smul_comm _ _⟩

@[to_additive]
instance smul_comm_class_finset' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α (finset β) (finset γ) :=
⟨λ a s t, coe_injective $ by simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]
instance smul_comm_class_finset'' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (finset α) β (finset γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (finset α) (finset β) (finset γ) :=
⟨λ s t u, coe_injective $ by simp_rw [coe_smul, smul_comm]⟩

@[to_additive]
instance is_scalar_tower [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α β (finset γ) :=
⟨λ a b s, by simp only [←image_smul, image_image, smul_assoc]⟩

variables [decidable_eq β]

@[to_additive]
instance is_scalar_tower' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α (finset β) (finset γ) :=
⟨λ a s t, coe_injective $ by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive]
instance is_scalar_tower'' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower (finset α) (finset β) (finset γ) :=
⟨λ a s t, coe_injective $ by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

instance is_central_scalar [has_smul α β] [has_smul αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (finset β) :=
⟨λ a s, coe_injective $ by simp only [coe_smul_finset, coe_smul, op_smul_eq_smul]⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`finset α` on `finset β`. -/
@[to_additive "An additive action of an additive monoid `α` on a type `β` gives an additive action
of `finset α` on `finset β`"]
protected def mul_action [decidable_eq α] [monoid α] [mul_action α β] :
  mul_action (finset α) (finset β) :=
{ mul_smul := λ _ _ _, image₂_assoc mul_smul,
  one_smul := λ s, image₂_singleton_left.trans $ by simp_rw [one_smul, image_id'] }

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `finset β`.
-/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action
on `finset β`."]
protected def mul_action_finset [monoid α] [mul_action α β] : mul_action α (finset β) :=
coe_injective.mul_action _ coe_smul_finset

localized "attribute [instance] finset.mul_action_finset finset.add_action_finset
  finset.mul_action finset.add_action" in pointwise

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `finset β`. -/
protected def distrib_mul_action_finset [monoid α] [add_monoid β] [distrib_mul_action α β] :
  distrib_mul_action α (finset β) :=
function.injective.distrib_mul_action ⟨coe, coe_zero, coe_add⟩ coe_injective coe_smul_finset

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mul_distrib_mul_action_finset [monoid α] [monoid β] [mul_distrib_mul_action α β] :
  mul_distrib_mul_action α (finset β) :=
function.injective.mul_distrib_mul_action ⟨coe, coe_one, coe_mul⟩ coe_injective coe_smul_finset

localized "attribute [instance] finset.distrib_mul_action_finset
  finset.mul_distrib_mul_action_finset" in pointwise

instance [decidable_eq α] [has_zero α] [has_mul α] [no_zero_divisors α] :
  no_zero_divisors (finset α) :=
coe_injective.no_zero_divisors _ coe_zero coe_mul

instance [has_zero α] [has_zero β] [has_smul α β] [no_zero_smul_divisors α β] :
  no_zero_smul_divisors (finset α) (finset β) :=
⟨λ s t h, begin
  by_contra' H,
  have hst : (s • t).nonempty := h.symm.subst zero_nonempty,
  simp_rw [←hst.of_smul_left.subset_zero_iff, ←hst.of_smul_right.subset_zero_iff, not_subset,
    mem_zero] at H,
  obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H,
  have := subset_of_eq h,
  exact (eq_zero_or_eq_zero_of_smul_eq_zero $ mem_zero.1 $ this $ smul_mem_smul hs ht).elim ha hb,
end⟩

instance no_zero_smul_divisors_finset [has_zero α] [has_zero β] [has_smul α β]
  [no_zero_smul_divisors α β] : no_zero_smul_divisors α (finset β) :=
coe_injective.no_zero_smul_divisors _ coe_zero coe_smul_finset

end instances

section left_cancel_semigroup
variables [left_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

@[to_additive] lemma pairwise_disjoint_smul_iff {s : set α} {t : finset α} :
  s.pairwise_disjoint (• t) ↔ (s ×ˢ t : set (α × α)).inj_on (λ p, p.1 * p.2) :=
by simp_rw [←pairwise_disjoint_coe, coe_smul_finset, set.pairwise_disjoint_smul_iff]

@[simp, to_additive] lemma card_singleton_mul : ({a} * t).card = t.card :=
card_image₂_singleton_left _ $ mul_right_injective _

@[to_additive] lemma singleton_mul_inter : {a} * (s ∩ t) = ({a} * s) ∩ ({a} * t) :=
image₂_singleton_inter _ _ $ mul_right_injective _

@[to_additive] lemma card_le_card_mul_left {s : finset α} (hs : s.nonempty) :
  t.card ≤ (s * t).card :=
card_le_card_image₂_left _ hs mul_right_injective

end left_cancel_semigroup

section
variables [right_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

@[simp, to_additive] lemma card_mul_singleton : (s * {a}).card = s.card :=
card_image₂_singleton_right _ $ mul_left_injective _

@[to_additive] lemma inter_mul_singleton : (s ∩ t) * {a} = (s * {a}) ∩ (t * {a}) :=
image₂_inter_singleton _ _ $ mul_left_injective _

@[to_additive] lemma card_le_card_mul_right {t : finset α} (ht : t.nonempty) :
  s.card ≤ (s * t).card :=
card_le_card_image₂_right _ ht mul_left_injective

end

open_locale pointwise

section group
variables [decidable_eq β] [group α] [mul_action α β] {s t : finset β} {a : α} {b : β}

@[simp, to_additive] lemma smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s :=
(mul_action.injective _).mem_finset_image

@[to_additive] lemma inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
by rw [←smul_mem_smul_finset_iff a, smul_inv_smul]

@[to_additive] lemma mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
by rw [←smul_mem_smul_finset_iff a, smul_inv_smul]

@[simp, to_additive] lemma smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t :=
image_subset_image_iff $ mul_action.injective _

@[to_additive] lemma smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
by { simp_rw ←coe_subset, push_cast, exact set.set_smul_subset_iff }

@[to_additive] lemma subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
by { simp_rw ←coe_subset, push_cast, exact set.subset_set_smul_iff }

end group

section group_with_zero
variables [decidable_eq β] [group_with_zero α] [mul_action α β] {s t : finset β} {a : α} {b : β}

@[simp] lemma smul_mem_smul_finset_iff₀ (ha : a ≠ 0) : a • b ∈ a • s ↔ b ∈ s :=
smul_mem_smul_finset_iff (units.mk0 a ha)

lemma inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
show _ ↔ _ ∈ units.mk0 a ha • _, from inv_smul_mem_iff

lemma mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
show _ ∈ (units.mk0 a ha)⁻¹ • _ ↔ _, from mem_inv_smul_finset_iff

@[simp] lemma smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from smul_finset_subset_smul_finset_iff

lemma smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from smul_finset_subset_iff

lemma subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
show _ ⊆ units.mk0 a ha • _ ↔ _, from subset_smul_finset_iff

lemma smul_univ₀ [fintype β] {s : finset α} (hs : ¬ s ⊆ 0) : s • (univ : finset β) = univ :=
coe_injective $ by { rw ←coe_subset at hs, push_cast at ⊢ hs, exact set.smul_univ₀ hs }

lemma smul_finset_univ₀ [fintype β] (ha : a ≠ 0) : a • (univ : finset β) = univ :=
coe_injective $ by {  push_cast, exact set.smul_set_univ₀ ha }

end group_with_zero

section smul_with_zero
variables [has_zero α] [has_zero β] [smul_with_zero α β] [decidable_eq β] {s : finset α}
  {t : finset β}

/-!
Note that we have neither `smul_with_zero α (finset β)` nor `smul_with_zero (finset α) (finset β)`
because `0 * ∅ ≠ 0`.
-/

lemma smul_zero_subset (s : finset α) : s • (0 : finset β) ⊆ 0 := by simp [subset_iff, mem_smul]
lemma zero_smul_subset (t : finset β) : (0 : finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]

lemma nonempty.smul_zero (hs : s.nonempty) : s • (0 : finset β) = 0 :=
s.smul_zero_subset.antisymm $ by simpa [mem_smul] using hs

lemma nonempty.zero_smul (ht : t.nonempty) : (0 : finset α) • t = 0 :=
t.zero_smul_subset.antisymm $ by simpa [mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
lemma zero_smul_finset {s : finset β} (h : s.nonempty) : (0 : α) • s = (0 : finset β) :=
coe_injective $ by simpa using @set.zero_smul_set α _ _ _ _ _ h

lemma zero_smul_finset_subset (s : finset β) : (0 : α) • s ⊆ 0 :=
image_subset_iff.2 $ λ x _, mem_zero.2 $ zero_smul α x

lemma zero_mem_smul_finset {t : finset β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
mem_smul_finset.2 ⟨0, h, smul_zero _⟩

variables [no_zero_smul_divisors α β] {a : α}

lemma zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.nonempty ∨ (0 : β) ∈ t ∧ s.nonempty :=
by { rw [←mem_coe, coe_smul, set.zero_mem_smul_iff], refl }

lemma zero_mem_smul_finset_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
by { rw [←mem_coe, coe_smul_finset, set.zero_mem_smul_set_iff ha, mem_coe], apply_instance }

end smul_with_zero

section monoid
variables [monoid α] [add_group β] [distrib_mul_action α β] [decidable_eq β] (a : α) (s : finset α)
  (t : finset β)

@[simp] lemma smul_finset_neg : a • -t = -(a • t) :=
by simp only [←image_smul, ←image_neg, function.comp, image_image, smul_neg]

@[simp] protected lemma smul_neg : s • -t = -(s • t) :=
by { simp_rw ←image_neg, exact image_image₂_right_comm smul_neg }

end monoid

section ring
variables [ring α] [add_comm_group β] [module α β] [decidable_eq β] {s : finset α} {t : finset β}
  {a : α}

@[simp] lemma neg_smul_finset : -a • t = -(a • t) :=
by simp only [←image_smul, ←image_neg, image_image, neg_smul]

@[simp] protected lemma neg_smul [decidable_eq α] : -s • t = -(s • t) :=
by { simp_rw ←image_neg, exact image₂_image_left_comm neg_smul }

end ring
end finset
