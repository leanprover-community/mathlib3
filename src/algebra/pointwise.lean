/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.module
import data.set.finite

/-!
# Pointwise addition, multiplication, and scalar multiplication of sets.

This file defines pointwise algebraic operations on sets.
* For a type `α` with multiplication, multiplication is defined on `set α` by taking
  `s * t` to be the set of all `x * y` where `x ∈ s` and `y ∈ t`. Similarly for addition.
* For `α` a semigroup, `set α` is a semigroup.
* If `α` is a (commutative) monoid, we define an alias `set_semiring α` for `set α`, which then
  becomes a (commutative) semiring with union as addition and pointwise multiplication as
  multiplication.
* For a type `β` with scalar multiplication by another type `α`, this
  file defines a scalar multiplication of `set β` by `set α` and a separate scalar
  multiplication of `set β` by `α`.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes
* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication

-/

namespace set
open function

variables {α : Type*} {β : Type*} {s s₁ s₂ t t₁ t₂ u : set α} {a b : α} {x y : β}

/-! Properties about 1 -/
@[to_additive]
instance [has_one α] : has_one (set α) := ⟨{1}⟩

@[simp, to_additive]
lemma singleton_one [has_one α] : ({1} : set α) = 1 := rfl

@[simp, to_additive]
lemma mem_one [has_one α] : a ∈ (1 : set α) ↔ a = 1 := iff.rfl

@[to_additive]
lemma one_mem_one [has_one α] : (1 : α) ∈ (1 : set α) := eq.refl _

@[simp, to_additive]
theorem one_subset [has_one α] : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

@[to_additive]
theorem one_nonempty [has_one α] : (1 : set α).nonempty := ⟨1, rfl⟩

@[simp, to_additive]
theorem image_one [has_one α] {f : α → β} : f '' 1 = {f 1} := image_singleton

/-! Properties about multiplication -/
@[to_additive]
instance [has_mul α] : has_mul (set α) := ⟨image2 has_mul.mul⟩

@[simp, to_additive]
lemma image2_mul [has_mul α] : image2 has_mul.mul s t = s * t := rfl

@[to_additive]
lemma mem_mul [has_mul α] : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a := iff.rfl

@[to_additive]
lemma mul_mem_mul [has_mul α] (ha : a ∈ s) (hb : b ∈ t) : a * b ∈ s * t := mem_image2_of_mem ha hb

@[to_additive add_image_prod]
lemma image_mul_prod [has_mul α] : (λ x : α × α, x.fst * x.snd) '' s.prod t = s * t := image_prod _

@[simp, to_additive]
lemma image_mul_left [group α] : (λ b, a * b) '' t = (λ b, a⁻¹ * b) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[simp, to_additive]
lemma image_mul_right [group α] : (λ a, a * b) '' t = (λ a, a * b⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[to_additive]
lemma image_mul_left' [group α] : (λ b, a⁻¹ * b) '' t = (λ b, a * b) ⁻¹' t := by simp

@[to_additive]
lemma image_mul_right' [group α] : (λ a, a * b⁻¹) '' t = (λ a, a * b) ⁻¹' t := by simp

@[simp, to_additive]
lemma preimage_mul_left_one [group α] : (λ b, a * b) ⁻¹' 1 = {a⁻¹} :=
by rw [← image_mul_left', image_one, mul_one]

@[simp, to_additive]
lemma preimage_mul_right_one [group α] : (λ a, a * b) ⁻¹' 1 = {b⁻¹} :=
by rw [← image_mul_right', image_one, one_mul]

@[to_additive]
lemma preimage_mul_left_one' [group α] : (λ b, a⁻¹ * b) ⁻¹' 1 = {a} := by simp

@[to_additive]
lemma preimage_mul_right_one' [group α] : (λ a, a * b) ⁻¹' 1 = {b⁻¹} := by simp

@[simp, to_additive]
lemma mul_singleton [has_mul α] : s * {b} = (λ a, a * b) '' s := image2_singleton_right

@[simp, to_additive]
lemma singleton_mul [has_mul α] : {a} * t = (λ b, a * b) '' t := image2_singleton_left

@[simp, to_additive]
lemma singleton_mul_singleton [has_mul α] : ({a} : set α) * {b} = {a * b} := image2_singleton

@[to_additive set.add_semigroup]
instance [semigroup α] : semigroup (set α) :=
{ mul_assoc :=
    by { intros, simp only [← image2_mul, image2_image2_left, image2_image2_right, mul_assoc] },
  ..set.has_mul }

@[to_additive set.add_monoid]
instance [monoid α] : monoid (set α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..set.semigroup,
  ..set.has_one }

@[to_additive]
protected lemma mul_comm [comm_semigroup α] : s * t = t * s :=
by simp only [← image2_mul, image2_swap _ s, mul_comm]

@[to_additive set.add_comm_monoid]
instance [comm_monoid α] : comm_monoid (set α) :=
{ mul_comm := λ _ _, set.mul_comm, ..set.monoid }

@[to_additive]
lemma singleton.is_mul_hom [has_mul α] : is_mul_hom (singleton : α → set α) :=
{ map_mul := λ a b, singleton_mul_singleton.symm }

@[simp, to_additive]
lemma empty_mul [has_mul α] : ∅ * s = ∅ := image2_empty_left

@[simp, to_additive]
lemma mul_empty [has_mul α] : s * ∅ = ∅ := image2_empty_right

@[to_additive]
lemma mul_subset_mul [has_mul α] (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ * s₂ ⊆ t₁ * t₂ :=
image2_subset h₁ h₂

@[to_additive]
lemma union_mul [has_mul α] : (s ∪ t) * u = (s * u) ∪ (t * u) := image2_union_left

@[to_additive]
lemma mul_union [has_mul α] : s * (t ∪ u) = (s * t) ∪ (s * u) := image2_union_right

@[to_additive]
lemma Union_mul_left_image [has_mul α] : (⋃ a ∈ s, (λ x, a * x) '' t) = s * t :=
Union_image_left _

@[to_additive]
lemma Union_mul_right_image [has_mul α] : (⋃ a ∈ t, (λ x, x * a) '' s) = s * t :=
Union_image_right _

@[simp, to_additive]
lemma univ_mul_univ [monoid α] : (univ : set α) * univ = univ :=
begin
  have : ∀x, ∃a b : α, a * b = x := λx, ⟨x, ⟨1, mul_one x⟩⟩,
  simpa only [mem_mul, eq_univ_iff_forall, mem_univ, true_and]
end

/-- `singleton` is a monoid hom. -/
@[to_additive singleton_add_hom "singleton is an add monoid hom"]
def singleton_hom [monoid α] : α →* set α :=
{ to_fun := singleton, map_one' := rfl, map_mul' := λ a b, singleton_mul_singleton.symm }

@[to_additive]
lemma nonempty.mul [has_mul α] : s.nonempty → t.nonempty → (s * t).nonempty := nonempty.image2

@[to_additive]
lemma finite.mul [has_mul α] (hs : finite s) (ht : finite t) : finite (s * t) :=
hs.image2 _ ht

/-- multiplication preserves finiteness -/
@[to_additive "addition preserves finiteness"]
def fintype_mul [has_mul α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  fintype (s * t : set α) :=
set.fintype_image2 _ s t

/-! Properties about inversion -/
@[to_additive set.has_neg'] -- todo: remove prime once name becomes available
instance [has_inv α] : has_inv (set α) :=
⟨preimage has_inv.inv⟩

@[simp, to_additive]
lemma mem_inv [has_inv α] : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := iff.rfl

@[to_additive]
lemma inv_mem_inv [group α] : a⁻¹ ∈ s⁻¹ ↔ a ∈ s :=
by simp only [mem_inv, inv_inv]

@[simp, to_additive]
lemma inv_preimage [has_inv α] : has_inv.inv ⁻¹' s = s⁻¹ := rfl

@[simp, to_additive]
lemma image_inv [group α] : has_inv.inv '' s = s⁻¹ :=
by { simp only [← inv_preimage], rw [image_eq_preimage_of_inverse]; intro; simp only [inv_inv] }

@[simp, to_additive]
lemma inter_inv [has_inv α] : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := preimage_inter

@[simp, to_additive]
lemma union_inv [has_inv α] : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := preimage_union

@[simp, to_additive]
lemma compl_inv [has_inv α] : (sᶜ)⁻¹ = (s⁻¹)ᶜ := preimage_compl

@[simp, to_additive]
protected lemma inv_inv [group α] : s⁻¹⁻¹ = s :=
by { simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id'] }

@[simp, to_additive]
protected lemma univ_inv [group α] : (univ : set α)⁻¹ = univ := preimage_univ

/-! Properties about scalar multiplication -/

/-- Scaling a set: multiplying every element by a scalar. -/
instance has_scalar_set [has_scalar α β] : has_scalar α (set β) :=
⟨λ a, image (has_scalar.smul a)⟩

@[simp]
lemma image_smul [has_scalar α β] {t : set β} : (λ x, a • x) '' t = a • t := rfl

lemma mem_smul_set [has_scalar α β] {t : set β} : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := iff.rfl

lemma smul_mem_smul_set [has_scalar α β] {t : set β} (hy : y ∈ t) : a • y ∈ a • t :=
⟨y, hy, rfl⟩

lemma smul_set_union [has_scalar α β] {s t : set β} : a • (s ∪ t) = a • s ∪ a • t :=
by simp only [← image_smul, image_union]

@[simp]
lemma smul_set_empty [has_scalar α β] (a : α) : a • (∅ : set β) = ∅ :=
by rw [← image_smul, image_empty]

lemma smul_set_mono [has_scalar α β] {s t : set β} (h : s ⊆ t) : a • s ⊆ a • t :=
by { simp only [← image_smul, image_subset, h] }

/-- Pointwise scalar multiplication by a set of scalars. -/
instance [has_scalar α β] : has_scalar (set α) (set β) := ⟨image2 has_scalar.smul⟩

@[simp]
lemma image2_smul [has_scalar α β] {t : set β} : image2 has_scalar.smul s t = s • t := rfl

lemma mem_smul [has_scalar α β] {t : set β} : x ∈ s • t ↔ ∃ a y, a ∈ s ∧ y ∈ t ∧ a • y = x :=
iff.rfl

lemma image_smul_prod [has_scalar α β] {t : set β} :
  (λ x : α × β, x.fst • x.snd) '' s.prod t = s • t :=
image_prod _

theorem range_smul_range [has_scalar α β] {ι κ : Type*} (b : ι → α) (c : κ → β) :
  range b • range c = range (λ p : ι × κ, b p.1 • c p.2) :=
ext $ λ x, ⟨λ hx, let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := set.mem_smul.1 hx in
  ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
λ ⟨⟨i, j⟩, h⟩, set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

lemma singleton_smul [has_scalar α β] {t : set β} : ({a} : set α) • t = a • t :=
image2_singleton_left

section monoid

/-! `set α` as a `(∪,*)`-semiring -/

/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
@[derive inhabited] def set_semiring (α : Type*) : Type* := set α

/-- The identitiy function `set α → set_semiring α`. -/
protected def up (s : set α) : set_semiring α := s
/-- The identitiy function `set_semiring α → set α`. -/
protected def set_semiring.down (s : set_semiring α) : set α := s
@[simp] protected lemma down_up {s : set α} : s.up.down = s := rfl
@[simp] protected lemma up_down {s : set_semiring α} : s.down.up = s := rfl

instance set_semiring.semiring [monoid α] : semiring (set_semiring α) :=
{ add := λ s t, (s ∪ t : set α),
  zero := (∅ : set α),
  add_assoc := union_assoc,
  zero_add := empty_union,
  add_zero := union_empty,
  add_comm := union_comm,
  zero_mul := λ s, empty_mul,
  mul_zero := λ s, mul_empty,
  left_distrib := λ _ _ _, mul_union,
  right_distrib := λ _ _ _, union_mul,
  ..set.monoid }

instance set_semiring.comm_semiring [comm_monoid α] : comm_semiring (set_semiring α) :=
{ ..set.comm_monoid, ..set_semiring.semiring }

/-- A multiplicative action of a monoid on a type β gives also a
 multiplicative action on the subsets of β. -/
instance mul_action_set [monoid α] [mul_action α β] : mul_action α (set β) :=
{ mul_smul := by { intros, simp only [← image_smul, image_image, ← mul_smul] },
  one_smul := by { intros, simp only [← image_smul, image_eta, one_smul, image_id'] },
  ..set.has_scalar_set }

section is_mul_hom
open is_mul_hom

variables [has_mul α] [has_mul β] (m : α → β) [is_mul_hom m]

@[to_additive]
lemma image_mul : m '' (s * t) = m '' s * m '' t :=
by { simp only [← image2_mul, image_image2, image2_image_left, image2_image_right, map_mul m] }

@[to_additive]
lemma preimage_mul_preimage_subset {s t : set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
by { rintros _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_mul _ _ _).symm ⟩ }

end is_mul_hom

/-- The image of a set under function is a ring homomorphism
with respect to the pointwise operations on sets. -/
def image_hom [monoid α] [monoid β] (f : α →* β) : set_semiring α →+* set_semiring β :=
{ to_fun := image f,
  map_zero' := image_empty _,
  map_one' := by simp only [← singleton_one, image_singleton, is_monoid_hom.map_one f],
  map_add' := image_union _,
  map_mul' := λ _ _, image_mul _ }

end monoid

end set

section

open set

variables {α : Type*} {β : Type*}

/-- A nonempty set in a semimodule is scaled by zero to the singleton
containing 0 in the semimodule. -/
lemma zero_smul_set [semiring α] [add_comm_monoid β] [semimodule α β] {s : set β} (h : s.nonempty) :
  (0 : α) • s = (0 : set β) :=
by simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

lemma mem_inv_smul_set_iff [field α] [mul_action α β] {a : α} (ha : a ≠ 0) (A : set β) (x : β) :
  x ∈ a⁻¹ • A ↔ a • x ∈ A :=
by simp only [← image_smul, mem_image, inv_smul_eq_iff ha, exists_eq_right]

lemma mem_smul_set_iff_inv_smul_mem [field α] [mul_action α β] {a : α} (ha : a ≠ 0) (A : set β)
  (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
by rw [← mem_inv_smul_set_iff $ inv_ne_zero ha, inv_inv']

end
