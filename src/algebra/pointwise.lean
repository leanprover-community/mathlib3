/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Pointwise addition and multiplication of sets
-/

import data.set.finite data.set.lattice group_theory.group_action

namespace set
open function

variables {α : Type*} {β : Type*} (f : α → β)

@[to_additive set.pointwise_zero]
def pointwise_one [has_one α] : has_one (set α) := ⟨{1}⟩

local attribute [instance] pointwise_one

@[simp, to_additive set.mem_pointwise_zero]
lemma mem_pointwise_one [has_one α] (a : α) :
  a ∈ (1 : set α) ↔ a = 1 :=
mem_singleton_iff

@[to_additive set.pointwise_add]
def pointwise_mul [has_mul α] : has_mul (set α) :=
  ⟨λ s t, {a | ∃ x ∈ s, ∃ y ∈ t, a = x * y}⟩

local attribute [instance] pointwise_one pointwise_mul pointwise_add

@[to_additive set.mem_pointwise_add]
lemma mem_pointwise_mul [has_mul α] {s t : set α} {a : α} :
  a ∈ s * t ↔ ∃ x ∈ s, ∃ y ∈ t, a = x * y := iff.rfl

@[to_additive set.add_mem_pointwise_add]
lemma mul_mem_pointwise_mul [has_mul α] {s t : set α} {a b : α} (ha : a ∈ s) (hb : b ∈ t) :
  a * b ∈ s * t := ⟨_, ha, _, hb, rfl⟩

@[to_additive set.pointwise_add_eq_image]
lemma pointwise_mul_eq_image [has_mul α] {s t : set α} :
  s * t = (λ x : α × α, x.fst * x.snd) '' s.prod t :=
set.ext $ λ a,
⟨ by { rintros ⟨_, _, _, _, rfl⟩, exact ⟨(_, _), mem_prod.mpr ⟨‹_›, ‹_›⟩, rfl⟩ },
  by { rintros ⟨_, _, rfl⟩, exact ⟨_, (mem_prod.mp ‹_›).1, _, (mem_prod.mp ‹_›).2, rfl⟩ }⟩

@[to_additive set.pointwise_add_finite]
lemma pointwise_mul_finite [has_mul α] {s t : set α} (hs : finite s) (ht : finite t) :
  finite (s * t) :=
by { rw pointwise_mul_eq_image, apply set.finite_image, exact set.finite_prod hs ht }

@[to_additive set.pointwise_add_add_semigroup]
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

@[to_additive set.pointwise_add_add_monoid]
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

@[to_additive set.singleton.is_add_hom]
def singleton.is_mul_hom [has_mul α] : is_mul_hom (singleton : α → set α) :=
{ map_mul := λ x y, set.ext $ λ a, by simp [mem_singleton_iff, mem_pointwise_mul] }

@[to_additive set.singleton.is_add_monoid_hom]
def singleton.is_monoid_hom [monoid α] : is_monoid_hom (singleton : α → set α) :=
{ map_one := rfl, ..singleton.is_mul_hom }

@[to_additive set.pointwise_neg]
def pointwise_inv [has_inv α] : has_inv (set α) :=
⟨λ s, {a | a⁻¹ ∈ s}⟩

@[simp, to_additive set.pointwise_add_empty]
lemma pointwise_mul_empty [has_mul α] (s : set α) :
  s * ∅ = ∅ :=
set.ext $ λ a, ⟨by {rintros ⟨_, _, _, _, rfl⟩, tauto}, false.elim⟩

@[simp, to_additive set.empty_pointwise_add]
lemma empty_pointwise_mul [has_mul α] (s : set α) :
  ∅ * s = ∅ :=
set.ext $ λ a, ⟨by {rintros ⟨_, _, _, _, rfl⟩, tauto}, false.elim⟩

@[to_additive set.pointwise_add_subset_add]
lemma pointwise_mul_subset_mul [has_mul α] {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
  s₁ * s₂ ⊆ t₁ * t₂ :=
by {rintros _ ⟨_, _, _, _, rfl⟩, exact ⟨_, h₁ ‹_›, _, h₂ ‹_›, rfl⟩ }

@[to_additive set.pointwise_add_union]
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

@[to_additive set.union_pointwise_add]
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

@[to_additive set.pointwise_add_eq_Union_add_left]
lemma pointwise_mul_eq_Union_mul_left [has_mul α] {s t : set α} : s * t = ⋃a∈s, (λx, a * x) '' t :=
by { ext y; split; simp only [mem_Union]; rintros ⟨a, ha, x, hx, ax⟩; exact ⟨a, ha, x, hx, ax.symm⟩ }

@[to_additive set.pointwise_add_eq_Union_add_right]
lemma pointwise_mul_eq_Union_mul_right [has_mul α] {s t : set α} : s * t = ⋃a∈t, (λx, x * a) '' s :=
by { ext y; split; simp only [mem_Union]; rintros ⟨a, ha, x, hx, ax⟩; exact ⟨x, hx, a, ha, ax.symm⟩ }

@[to_additive set.pointwise_add_ne_empty]
lemma pointwise_mul_ne_empty [has_mul α] {s t : set α} : s ≠ ∅ → t ≠ ∅ → s * t ≠ ∅ :=
begin
  simp only [ne_empty_iff_exists_mem],
  rintros ⟨x, hx⟩ ⟨y, hy⟩,
  exact ⟨x * y, mul_mem_pointwise_mul hx hy⟩
end

@[simp, to_additive univ_add_univ]
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

attribute [to_additive set.pointwise_add_fintype] set.pointwise_mul_fintype

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

section is_mul_hom
open is_mul_hom

variables [has_mul α] [has_mul β] (m : α → β) [is_mul_hom m]

@[to_additive is_add_hom.image_add]
lemma image_pointwise_mul (s t : set α) : m '' (s * t) = m '' s * m '' t :=
set.ext $ assume y,
begin
  split,
  { rintros ⟨_, ⟨_, _, _, _, rfl⟩, rfl⟩,
    refine ⟨_, mem_image_of_mem _ ‹_›, _, mem_image_of_mem _ ‹_›, map_mul _ _ _⟩ },
  { rintros ⟨_, ⟨_, _, rfl⟩, _, ⟨_, _, rfl⟩, rfl⟩,
    refine ⟨_, ⟨_, ‹_›, _, ‹_›, rfl⟩, map_mul _ _ _⟩ }
end

@[to_additive is_add_hom.preimage_add_preimage_subset]
lemma preimage_pointwise_mul_preimage_subset (s t : set β) : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
begin
  rintros _ ⟨_, _, _, _, rfl⟩,
  exact ⟨_, ‹_›, _, ‹_›, map_mul _ _ _⟩,
end

end is_mul_hom

variables [monoid α] [monoid β] [is_monoid_hom f]

def pointwise_mul_image_is_semiring_hom : is_semiring_hom (image f) :=
{ map_zero := image_empty _,
  map_one := by erw [image_singleton, is_monoid_hom.map_one f]; refl,
  map_add := image_union _,
  map_mul := image_pointwise_mul _ }

local attribute [instance] singleton.is_monoid_hom

def pointwise_mul_action : mul_action α (set α) :=
{ smul := λ a s, ({a} : set α) * s,
  one_smul := one_mul,
  mul_smul := λ _ _ _, show {_} * _ = _,
    by { erw is_monoid_hom.map_mul (singleton : α → set α), apply mul_assoc } }

local attribute [instance] pointwise_mul_action

lemma mem_smul_set {a : α} {s : set α} {x : α} :
  x ∈ a • s ↔ ∃ y ∈ s, x = a * y :=
by { erw mem_pointwise_mul, simp }

lemma smul_set_eq_image {a : α} {s : set α} :
  a • s = (λ b, a * b) '' s :=
set.ext $ λ x,
begin
  simp only [mem_smul_set, exists_prop, mem_image],
  apply exists_congr,
  intro y,
  apply and_congr iff.rfl,
  split; exact eq.symm
end

end monoid

end set
