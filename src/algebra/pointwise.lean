/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.module

/-!

# Pointwise addition, multiplication, and scalar multiplication of sets.

This file defines `pointwise_mul`: for a type `α` with multiplication,
multiplication is defined on `set α` by taking `s * t` to be the set
of all `x * y` where `x ∈ s` and `y ∈ t`.

Pointwise multiplication on `set α` where `α` is a semigroup makes
`set α` into a semigroup. If `α` is additionally a (commutative)
monoid, `set α` becomes a (commutative) semiring with union as
addition. These are given by `pointwise_mul_semigroup` and
`pointwise_mul_semiring`.

Definitions and results are also transported to the additive theory
via `to_additive`.

For a type `β` with scalar multiplication by another type `α`, this
file defines `pointwise_smul`. Separately it defines `smul_set`, for
scalar multiplication of `set β` by a single term of type `α`.

## Implementation notes

Elsewhere, one should register local instances to use the definitions
in this file.

-/

namespace set
open function

variables {α : Type*} {β : Type*} (f : α → β)

@[to_additive]
def pointwise_one [has_one α] : has_one (set α) := ⟨{1}⟩

local attribute [instance] pointwise_one

@[simp, to_additive]
lemma mem_pointwise_one [has_one α] (a : α) :
  a ∈ (1 : set α) ↔ a = 1 :=
mem_singleton_iff

@[to_additive]
def pointwise_mul [has_mul α] : has_mul (set α) :=
  ⟨λ s t, {a | ∃ x ∈ s, ∃ y ∈ t, a = x * y}⟩

local attribute [instance] pointwise_one pointwise_mul pointwise_add

@[to_additive]
lemma mem_pointwise_mul [has_mul α] {s t : set α} {a : α} :
  a ∈ s * t ↔ ∃ x ∈ s, ∃ y ∈ t, a = x * y := iff.rfl

@[to_additive]
lemma mul_mem_pointwise_mul [has_mul α] {s t : set α} {a b : α} (ha : a ∈ s) (hb : b ∈ t) :
  a * b ∈ s * t := ⟨_, ha, _, hb, rfl⟩

@[to_additive]
lemma pointwise_mul_eq_image [has_mul α] {s t : set α} :
  s * t = (λ x : α × α, x.fst * x.snd) '' s.prod t :=
set.ext $ λ a,
⟨ by { rintros ⟨_, _, _, _, rfl⟩, exact ⟨(_, _), mem_prod.mpr ⟨‹_›, ‹_›⟩, rfl⟩ },
  by { rintros ⟨_, _, rfl⟩, exact ⟨_, (mem_prod.mp ‹_›).1, _, (mem_prod.mp ‹_›).2, rfl⟩ }⟩

@[to_additive]
lemma pointwise_mul_finite [has_mul α] {s t : set α} (hs : finite s) (ht : finite t) :
  finite (s * t) :=
by { rw pointwise_mul_eq_image, exact (hs.prod ht).image _ }

@[to_additive pointwise_add_add_semigroup]
def pointwise_mul_semigroup [semigroup α] : semigroup (set α) :=
{ mul_assoc := λ _ _ _, set.ext $ λ _,
  begin
    split,
    { rintros ⟨_, ⟨_, _, _, _, rfl⟩, _, _, rfl⟩,
      exact ⟨_, ‹_›, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, mul_assoc _ _ _⟩ },
    { rintros ⟨_, _, _, ⟨_, _, _, _, rfl⟩, rfl⟩,
      exact ⟨_, ⟨_, ‹_›, _, ‹_›, rfl⟩, _, ‹_›, (mul_assoc _ _ _).symm⟩ }
  end,
  ..pointwise_mul }

@[to_additive pointwise_add_add_monoid]
def pointwise_mul_monoid [monoid α] : monoid (set α) :=
{ one_mul := λ s, set.ext $ λ a,
    ⟨by {rintros ⟨_, _, _, _, rfl⟩, simp * at *},
     λ h, ⟨1, mem_singleton 1, a, h, (one_mul a).symm⟩⟩,
  mul_one := λ s, set.ext $ λ a,
    ⟨by {rintros ⟨_, _, _, _, rfl⟩, simp * at *},
     λ h, ⟨a, h, 1, mem_singleton 1, (mul_one a).symm⟩⟩,
  ..pointwise_mul_semigroup,
  ..pointwise_one }

local attribute [instance] pointwise_mul_monoid

@[to_additive]
lemma singleton.is_mul_hom [has_mul α] : is_mul_hom (singleton : α → set α) :=
{ map_mul := λ x y, set.ext $ λ a, by simp [mem_singleton_iff, mem_pointwise_mul] }

@[to_additive is_add_monoid_hom]
lemma singleton.is_monoid_hom [monoid α] : is_monoid_hom (singleton : α → set α) :=
{ map_one := rfl, ..singleton.is_mul_hom }

@[to_additive]
def pointwise_inv [has_inv α] : has_inv (set α) :=
⟨λ s, {a | a⁻¹ ∈ s}⟩

@[simp, to_additive]
lemma pointwise_mul_empty [has_mul α] (s : set α) :
  s * ∅ = ∅ :=
set.ext $ λ a, ⟨by {rintros ⟨_, _, _, _, rfl⟩, tauto}, false.elim⟩

@[simp, to_additive]
lemma empty_pointwise_mul [has_mul α] (s : set α) :
  ∅ * s = ∅ :=
set.ext $ λ a, ⟨by {rintros ⟨_, _, _, _, rfl⟩, tauto}, false.elim⟩

@[to_additive]
lemma pointwise_mul_subset_mul [has_mul α] {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
  s₁ * s₂ ⊆ t₁ * t₂ :=
by {rintros _ ⟨_, _, _, _, rfl⟩, exact ⟨_, h₁ ‹_›, _, h₂ ‹_›, rfl⟩ }

@[to_additive]
lemma pointwise_mul_union [has_mul α] (s t u : set α) :
  s * (t ∪ u) = (s * t) ∪ (s * u) :=
begin
  ext a, split,
  { rintros ⟨_, _, _, H, rfl⟩,
    cases H; [left, right]; exact ⟨_, ‹_›, _, ‹_›, rfl⟩ },
  { intro H,
    cases H with H H;
    { rcases H with ⟨_, _, _, _, rfl⟩,
      refine ⟨_, ‹_›, _, _, rfl⟩,
      erw mem_union,
      simp * } }
end

@[to_additive]
lemma union_pointwise_mul [has_mul α] (s t u : set α) :
  (s ∪ t) * u = (s * u) ∪ (t * u) :=
begin
  ext a, split,
  { rintros ⟨_, H, _, _, rfl⟩,
    cases H; [left, right]; exact ⟨_, ‹_›, _, ‹_›, rfl⟩ },
  { intro H,
    cases H with H H;
    { rcases H with ⟨_, _, _, _, rfl⟩;
      refine ⟨_, _, _, ‹_›, rfl⟩;
      erw mem_union;
      simp * } }
end

@[to_additive]
lemma pointwise_mul_eq_Union_mul_left [has_mul α] {s t : set α} : s * t = ⋃a∈s, (λx, a * x) '' t :=
by { ext y; split; simp only [mem_Union]; rintros ⟨a, ha, x, hx, ax⟩; exact ⟨a, ha, x, hx, ax.symm⟩ }

@[to_additive]
lemma pointwise_mul_eq_Union_mul_right [has_mul α] {s t : set α} : s * t = ⋃a∈t, (λx, x * a) '' s :=
by { ext y; split; simp only [mem_Union]; rintros ⟨a, ha, x, hx, ax⟩; exact ⟨x, hx, a, ha, ax.symm⟩ }

@[to_additive]
lemma nonempty.pointwise_mul [has_mul α] {s t : set α} : s.nonempty → t.nonempty → (s * t).nonempty
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x * y, ⟨x, hx, y, hy, rfl⟩⟩

@[simp, to_additive]
lemma univ_pointwise_mul_univ [monoid α] : (univ : set α) * univ = univ :=
begin
  have : ∀x, ∃a b : α, x = a * b := λx, ⟨x, ⟨1, (mul_one x).symm⟩⟩,
  show {a | ∃ x ∈ univ, ∃ y ∈ univ, a = x * y} = univ,
  simpa [eq_univ_iff_forall]
end

def pointwise_mul_fintype [has_mul α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  fintype (s * t : set α) := by { rw pointwise_mul_eq_image, apply set.fintype_image }

def pointwise_add_fintype [has_add α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  fintype (s + t : set α) := by { rw pointwise_add_eq_image, apply set.fintype_image }

attribute [to_additive] set.pointwise_mul_fintype

/-- Pointwise scalar multiplication by a set of scalars. -/
def pointwise_smul [has_scalar α β] : has_scalar (set α) (set β) :=
  ⟨λ s t, { x | ∃ a ∈ s, ∃ y ∈ t, x  = a • y }⟩

/-- Scaling a set: multiplying every element by a scalar. -/
def smul_set [has_scalar α β] : has_scalar α (set β) :=
  ⟨λ a s, { x | ∃ y ∈ s, x = a • y }⟩

local attribute [instance] pointwise_smul smul_set

lemma mem_smul_set [has_scalar α β] (a : α) (s : set β) (x : β) :
  x ∈ a • s ↔ ∃ y ∈ s, x = a • y := iff.rfl

lemma smul_set_eq_image [has_scalar α β] (a : α) (s : set β) :
  a • s = (λ x, a • x) '' s :=
set.ext $ λ x, iff.intro
  (λ ⟨_, hy₁, hy₂⟩, ⟨_, hy₁, hy₂.symm⟩)
  (λ ⟨_, hy₁, hy₂⟩, ⟨_, hy₁, hy₂.symm⟩)

lemma smul_set_eq_pointwise_smul_singleton [has_scalar α β]
  (a : α) (s : set β) : a • s = ({a} : set α) • s :=
set.ext $ λ x, iff.intro
  (λ ⟨_, h⟩, ⟨a, mem_singleton _, _, h⟩)
  (λ ⟨_, h, y, hy, hx⟩, ⟨_, hy, by {
    rw mem_singleton_iff at h; rwa h at hx }⟩)

lemma smul_mem_smul_set [has_scalar α β]
  (a : α) {s : set β} {y : β} (hy : y ∈ s) : a • y ∈ a • s :=
by rw mem_smul_set; use [y, hy]

lemma smul_set_union [has_scalar α β] (a : α) (s t : set β) :
  a • (s ∪ t) = a • s ∪ a • t :=
by simp only [smul_set_eq_image, image_union]

@[simp] lemma smul_set_empty [has_scalar α β] (a : α) :
  a • (∅ : set β) = ∅ :=
by rw [smul_set_eq_image, image_empty]

lemma smul_set_mono [has_scalar α β]
  (a : α) {s t : set β} (h : s ⊆ t) : a • s ⊆ a • t :=
by { rw [smul_set_eq_image, smul_set_eq_image], exact image_subset _ h }

section monoid

def pointwise_mul_semiring [monoid α] : semiring (set α) :=
{ add := (⊔),
  zero := ∅,
  add_assoc := set.union_assoc,
  zero_add := set.empty_union,
  add_zero := set.union_empty,
  add_comm := set.union_comm,
  zero_mul := empty_pointwise_mul,
  mul_zero := pointwise_mul_empty,
  left_distrib := pointwise_mul_union,
  right_distrib := union_pointwise_mul,
  ..pointwise_mul_monoid }

def pointwise_mul_comm_semiring [comm_monoid α] : comm_semiring (set α) :=
{ mul_comm := λ s t, set.ext $ λ a,
  by split; { rintros ⟨_, _, _, _, rfl⟩, exact ⟨_, ‹_›, _, ‹_›, mul_comm _ _⟩ },
  ..pointwise_mul_semiring }

local attribute [instance] pointwise_mul_semiring

def comm_monoid [comm_monoid α] : comm_monoid (set α) :=
@comm_semiring.to_comm_monoid (set α) pointwise_mul_comm_semiring

def add_comm_monoid [add_comm_monoid α] : add_comm_monoid (set α) :=
show @add_comm_monoid (additive (set (multiplicative α))),
from @additive.add_comm_monoid _ set.comm_monoid

attribute [to_additive set.add_comm_monoid] set.comm_monoid

/-- A multiplicative action of a monoid on a type β gives also a
 multiplicative action on the subsets of β. -/
def smul_set_action [monoid α] [mul_action α β] :
  mul_action α (set β) :=
{ smul     := λ a s, a • s,
  mul_smul := λ a b s, set.ext $ λ x, iff.intro
    (λ ⟨_, hy, _⟩, ⟨b • _, smul_mem_smul_set _ hy, by rwa ←mul_smul⟩)
    (λ ⟨_, hy, _⟩, let ⟨_, hz, h⟩ := (mem_smul_set _ _ _).2 hy in
      ⟨_, hz, by rwa [mul_smul, ←h]⟩),
  one_smul := λ b, set.ext $ λ x, iff.intro
    (λ ⟨_, _, h⟩, by { rw [one_smul] at h; rwa h })
    (λ h, ⟨_, h, by rw one_smul⟩) }

section is_mul_hom
open is_mul_hom

variables [has_mul α] [has_mul β] (m : α → β) [is_mul_hom m]

@[to_additive]
lemma image_pointwise_mul (s t : set α) : m '' (s * t) = m '' s * m '' t :=
set.ext $ assume y,
begin
  split,
  { rintros ⟨_, ⟨_, _, _, _, rfl⟩, rfl⟩,
    refine ⟨_, mem_image_of_mem _ ‹_›, _, mem_image_of_mem _ ‹_›, map_mul _ _ _⟩ },
  { rintros ⟨_, ⟨_, _, rfl⟩, _, ⟨_, _, rfl⟩, rfl⟩,
    refine ⟨_, ⟨_, ‹_›, _, ‹_›, rfl⟩, map_mul _ _ _⟩ }
end

@[to_additive]
lemma preimage_pointwise_mul_preimage_subset (s t : set β) : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
begin
  rintros _ ⟨_, _, _, _, rfl⟩,
  exact ⟨_, ‹_›, _, ‹_›, map_mul _ _ _⟩,
end

end is_mul_hom

variables [monoid α] [monoid β] [is_monoid_hom f]

/--
The image of a set under function is a ring homomorphism
with respect to the pointwise operations on sets.
-/
def pointwise_mul_image_ring_hom : set α →+* set β :=
{ to_fun := image f,
  map_zero' := image_empty _,
  map_one' := by erw [image_singleton, is_monoid_hom.map_one f]; refl,
  map_add' := image_union _,
  map_mul' := image_pointwise_mul _ }

end monoid

end set

section

open set

variables {α : Type*} {β : Type*}

local attribute [instance] set.smul_set

/-- A nonempty set in a semimodule is scaled by zero to the singleton
containing 0 in the semimodule. -/
lemma zero_smul_set [semiring α] [add_comm_monoid β] [semimodule α β]
  {s : set β} (h : s.nonempty) : (0 : α) • s = {(0 : β)} :=
set.ext $ λ x, iff.intro
(λ ⟨_, _, hx⟩, mem_singleton_iff.mpr (by { rwa [hx, zero_smul] }))
(λ hx, let ⟨_, hs⟩ := h in
  ⟨_, hs, by { rw mem_singleton_iff at hx; rw [hx, zero_smul] }⟩)

lemma mem_inv_smul_set_iff [field α] [mul_action α β]
  {a : α} (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
iff.intro
  (λ ⟨y, hy, h⟩, by rwa [h, ←mul_smul, mul_inv_cancel ha, one_smul])
  (λ h, ⟨_, h, by rw [←mul_smul, inv_mul_cancel ha, one_smul]⟩)

lemma mem_smul_set_iff_inv_smul_mem [field α] [mul_action α β]
  {a : α} (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
by conv_lhs { rw ← inv_inv' a };
   exact (mem_inv_smul_set_iff (inv_ne_zero ha) _ _)

end
