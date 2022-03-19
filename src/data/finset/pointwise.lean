/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import data.finset.preimage
import data.set.pointwise

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For finsets `s` and `t` and scalar `a`:
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

We define `set_semiring α`, an alias of `set α`, which we endow with `∪` as addition and `*` as
multiplication. If `α` is a (commutative) monoid, `set_semiring α` is a (commutative) semiring.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## TODO

Add the missing operations.

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

open function
open_locale pointwise

variables {F α β γ : Type*}
namespace finset
variables {a : α} {s s₁ s₂ t t₁ t₂ : finset α}

/-- The finset `(1 : finset α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive /-"The finset `(0 : finset α)` is defined as `{0}` in locale `pointwise`. "-/]
protected def has_one [has_one α] : has_one (finset α) := ⟨{1}⟩

localized "attribute [instance] finset.has_one finset.has_zero" in pointwise

@[simp, to_additive]
lemma mem_one [has_one α] : a ∈ (1 : finset α) ↔ a = 1 :=
by simp [has_one.one]

@[simp, to_additive]
theorem one_subset [has_one α] : (1 : finset α) ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

@[simp, to_additive]
lemma coe_one [has_one α] : ↑(1 : finset α) = (1 : set α) := coe_singleton 1

section decidable_eq
variables [decidable_eq α]

/-- The pointwise product of two finite sets `s` and `t`:
`st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
@[to_additive /-"The pointwise sum of two finite sets `s` and `t`:
`s + t = { x + y | x ∈ s, y ∈ t }`. "-/]
protected def has_mul [has_mul α] : has_mul (finset α) :=
⟨λ s t, (s.product t).image (λ p : α × α, p.1 * p.2)⟩

localized "attribute [instance] finset.has_mul finset.has_add" in pointwise

section has_mul
variables [has_mul α]

@[to_additive]
lemma mul_def : s * t = (s.product t).image (λ p : α × α, p.1 * p.2) := rfl

@[to_additive]
lemma mem_mul {x : α} : x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [finset.mul_def, and.assoc, mem_image, exists_prop, prod.exists, mem_product] }

@[simp, norm_cast, to_additive]
lemma coe_mul (s t : finset α) : (↑(s * t) : set α) = ↑s * ↑t :=
by { ext, simp only [mem_mul, set.mem_mul, mem_coe] }

@[to_additive]
lemma mul_mem_mul {x y : α} (hx : x ∈ s) (hy : y ∈ t) : x * y ∈ s * t :=
by { simp only [finset.mem_mul], exact ⟨x, y, hx, hy, rfl⟩ }

@[to_additive]
lemma mul_card_le : (s * t).card ≤ s.card * t.card :=
by { convert finset.card_image_le, rw [finset.card_product, mul_comm] }

@[simp, to_additive] lemma empty_mul (s : finset α) : ∅ * s = ∅ :=
eq_empty_of_forall_not_mem (by simp [mem_mul])

@[simp, to_additive] lemma mul_empty (s : finset α) : s * ∅ = ∅ :=
eq_empty_of_forall_not_mem (by simp [mem_mul])

@[simp, to_additive]
lemma mul_nonempty_iff (s t : finset α) : (s * t).nonempty ↔ s.nonempty ∧ t.nonempty :=
by simp [finset.mul_def]

@[to_additive, mono] lemma mul_subset_mul  (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ * t₁ ⊆ s₂ * t₂ :=
image_subset_image (product_subset_product hs ht)

attribute [mono] add_subset_add

@[simp, to_additive]
lemma mul_singleton (a : α) : s * {a} = s.image (* a) :=
by { rw [mul_def, product_singleton, map_eq_image, image_image], refl }

@[simp, to_additive]
lemma singleton_mul (a : α) : {a} * s = s.image ((*) a) :=
by { rw [mul_def, singleton_product, map_eq_image, image_image], refl }

@[simp, to_additive]
lemma singleton_mul_singleton (a b : α) : ({a} : finset α) * {b} = {a * b} :=
by rw [mul_def, singleton_product_singleton, image_singleton]

end has_mul

section mul_zero_class
variables [mul_zero_class α]

lemma mul_zero_subset (s : finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]

lemma zero_mul_subset (s : finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]

lemma nonempty.mul_zero (hs : s.nonempty) : s * 0 = 0 :=
s.mul_zero_subset.antisymm $ by simpa [finset.mem_mul] using hs

lemma nonempty.zero_mul (hs : s.nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm $ by simpa [finset.mem_mul] using hs

lemma singleton_zero_mul (s : finset α) :
  {(0 : α)} * s ⊆ {0} :=
by simp [subset_iff, mem_mul]

end mul_zero_class
end decidable_eq

open_locale pointwise
variables {u : finset α} {b : α} {x y : β}

@[to_additive]
lemma singleton_one [has_one α] : ({1} : finset α) = 1 := rfl

@[to_additive]
lemma one_mem_one [has_one α] : (1 : α) ∈ (1 : finset α) := by simp [has_one.one]

@[to_additive]
theorem one_nonempty [has_one α] : (1 : finset α).nonempty := ⟨1, one_mem_one⟩

@[simp, to_additive]
theorem image_one [decidable_eq β] [has_one α] {f : α → β} : image f 1 = {f 1} :=
image_singleton f 1

@[to_additive add_image_prod]
lemma image_mul_prod [decidable_eq α] [has_mul α] :
  image (λ x : α × α, x.fst * x.snd) (s.product t) = s * t := rfl

@[simp, to_additive]
lemma image_mul_left [decidable_eq α] [group α] :
  image (λ b, a * b) t = preimage t (λ b, a⁻¹ * b) (assume x hx y hy, (mul_right_inj a⁻¹).mp) :=
coe_injective $ by simp

@[simp, to_additive]
lemma image_mul_right [decidable_eq α] [group α] :
  image (* b) t = preimage t (* b⁻¹) (assume x hx y hy, (mul_left_inj b⁻¹).mp) :=
coe_injective $ by simp

@[to_additive]
lemma image_mul_left' [decidable_eq α] [group α] :
  image (λ b, a⁻¹ * b) t = preimage t (λ b, a * b) (assume x hx y hy, (mul_right_inj a).mp) :=
by simp

@[to_additive]
lemma image_mul_right' [decidable_eq α] [group α] :
  image (* b⁻¹) t = preimage t (* b) (assume x hx y hy, (mul_left_inj b).mp) :=
by simp

@[simp, to_additive]
lemma preimage_mul_left_singleton [group α] :
  preimage {b} ((*) a) (assume x hx y hy, (mul_right_inj a).mp) = {a⁻¹ * b} :=
by { classical, rw [← image_mul_left', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_right_singleton [group α] :
  preimage {b} (* a) (assume x hx y hy, (mul_left_inj a).mp) = {b * a⁻¹} :=
by { classical, rw [← image_mul_right', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_left_one [group α] :
  preimage 1 (λ b, a * b) (assume x hx y hy, (mul_right_inj a).mp) = {a⁻¹} :=
by {classical, rw [← image_mul_left', image_one, mul_one] }

@[simp, to_additive]
lemma preimage_mul_right_one [group α] :
  preimage 1 (* b) (assume x hx y hy, (mul_left_inj b).mp) = {b⁻¹} :=
by {classical, rw [← image_mul_right', image_one, one_mul] }

@[to_additive]
lemma preimage_mul_left_one' [group α] :
  preimage 1 (λ b, a⁻¹ * b) (assume x hx y hy, (mul_right_inj _).mp) = {a} := by simp

@[to_additive]
lemma preimage_mul_right_one' [group α] :
  preimage 1 (* b⁻¹) (assume x hx y hy, (mul_left_inj _).mp) = {b} := by simp

@[to_additive]
protected lemma mul_comm [decidable_eq α] [comm_semigroup α] : s * t = t * s :=
by exact_mod_cast mul_comm (s : set α) t

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_zero_class` under pointwise operations if `α` is."-/]
protected def mul_one_class [decidable_eq α] [mul_one_class α] : mul_one_class (finset α) :=
function.injective.mul_one_class _ coe_injective (coe_singleton 1) (by simp)

/-- `finset α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_semigroup` under pointwise operations if `α` is. "-/]
protected def semigroup [decidable_eq α] [semigroup α] : semigroup (finset α) :=
function.injective.semigroup _ coe_injective (by simp)

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. -/
protected def has_nsmul [decidable_eq α] [add_monoid α] : has_scalar ℕ (finset α) :=
{ smul := λ n s, nsmul_rec n s }

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`finset`. -/
@[to_additive]
protected def has_npow [decidable_eq α] [monoid α] : has_pow (finset α) ℕ :=
{ pow := λ s n, npow_rec n s }

localized "attribute [instance] finset.has_nsmul finset.has_npow" in pointwise

@[simp, to_additive]
lemma coe_pow [decidable_eq α] [monoid α] (s : finset α) (n : ℕ) : ↑(s ^ n) = (s ^ n : set α) :=
begin
  change ↑(npow_rec n s) = _,
  induction n with n ih,
  { rw [npow_rec, pow_zero, coe_one] },
  { rw [npow_rec, pow_succ, coe_mul, ih], }
end

/-- `finset α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_monoid` under pointwise operations if `α` is. "-/]
protected def monoid [decidable_eq α] [monoid α] : monoid (finset α) :=
function.injective.monoid _ coe_injective coe_one coe_mul coe_pow

/-- `finset α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_comm_monoid` under pointwise operations if `α` is. "-/]
protected def comm_monoid [decidable_eq α] [comm_monoid α] : comm_monoid (finset α) :=
function.injective.comm_monoid _ coe_injective coe_one coe_mul coe_pow

localized "attribute [instance] finset.mul_one_class finset.add_zero_class finset.semigroup
  finset.add_semigroup finset.monoid finset.add_monoid finset.comm_monoid finset.add_comm_monoid"
  in pointwise

open_locale classical

/-- If a finset `U` contained in the product of two sets `S * S'`, we can find two finsets `T`, `T'`
such that `U ⊆ T * T'` and `T * T' ⊆ S * S'`. -/
@[to_additive "If a finset `U` contained in the product of two sets `S * S'`, we can find two
finsets `T`, `T'` such that `U ⊆ T * T'` and `T * T' ⊆ S * S'`."]
lemma subset_mul {M : Type*} [monoid M] {S : set M} {S' : set M} {U : finset M} (f : ↑U ⊆ S * S') :
  ∃ (T T' : finset M), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ U ⊆ T * T' :=
begin
  apply finset.induction_on' U,
  { use [∅, ∅], simp only [finset.empty_subset, finset.coe_empty, set.empty_subset, and_self], },
  rintros a s haU hs has ⟨T, T', hS, hS', h⟩,
  obtain ⟨x, y, hx, hy, ha⟩ := set.mem_mul.1 (f haU),
  use [insert x T, insert y T'],
  simp only [finset.coe_insert],
  repeat { rw [set.insert_subset], },
  use [hx, hS, hy, hS'],
  refine finset.insert_subset.mpr ⟨_, _⟩,
  { rw finset.mem_mul,
    use [x,y],
    simpa only [true_and, true_or, eq_self_iff_true, finset.mem_insert], },
  { suffices g : (s : set M) ⊆ insert x T * insert y T', { norm_cast at g, assumption, },
    transitivity ↑(T * T'),
    apply h,
    rw finset.coe_mul,
    apply set.mul_subset_mul (set.subset_insert x T) (set.subset_insert y T'), },
end

end finset
