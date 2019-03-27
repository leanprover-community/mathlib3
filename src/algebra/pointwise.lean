/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Pointwise addition and multiplication of sets
-/

import data.set.lattice
import algebra.group
import group_theory.subgroup

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

local attribute [instance] pointwise_one pointwise_mul

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

def pointwise_add_add_semigroup [add_semigroup α] : add_semigroup (set α) :=
{ add_assoc := λ _ _ _, set.ext $ λ _,
  begin
    split,
    { rintros ⟨_, ⟨_, _, _, _, rfl⟩, _, _, rfl⟩,
      exact ⟨_, ‹_›, _, ⟨_, ‹_›, _, ‹_›, rfl⟩, add_assoc _ _ _⟩ },
    { rintros ⟨_, _, _, ⟨_, _, _, _, rfl⟩, rfl⟩,
      exact ⟨_, ⟨_, ‹_›, _, ‹_›, rfl⟩, _, ‹_›, (add_assoc _ _ _).symm⟩ }
  end,
  ..pointwise_add }

attribute [to_additive set.pointwise_add_add_semigroup._proof_1] pointwise_mul_semigroup._proof_1
attribute [to_additive set.pointwise_add_add_semigroup] pointwise_mul_semigroup

def pointwise_mul_monoid [monoid α] : monoid (set α) :=
{ one_mul := λ s, set.ext $ λ a,
    ⟨by {rintros ⟨_, _, _, _, rfl⟩, simp * at *},
     λ h, ⟨1, mem_singleton 1, a, h, (one_mul a).symm⟩⟩,
  mul_one := λ s, set.ext $ λ a,
    ⟨by {rintros ⟨_, _, _, _, rfl⟩, simp * at *},
     λ h, ⟨a, h, 1, mem_singleton 1, (mul_one a).symm⟩⟩,
  ..pointwise_mul_semigroup,
  ..pointwise_one }

def pointwise_add_add_monoid [add_monoid α] : add_monoid (set α) :=
{ zero_add := λ s, set.ext $ λ a,
    ⟨by {rintros ⟨_, _, _, _, rfl⟩, simp * at *},
     λ h, ⟨0, mem_singleton 0, a, h, (zero_add a).symm⟩⟩,
  add_zero := λ s, set.ext $ λ a,
    ⟨by {rintros ⟨_, _, _, _, rfl⟩, simp * at *},
     λ h, ⟨a, h, 0, mem_singleton 0, (add_zero a).symm⟩⟩,
  ..pointwise_add_add_semigroup,
  ..pointwise_zero }

attribute [to_additive set.pointwise_add_add_monoid._proof_1] pointwise_mul_monoid._proof_1
attribute [to_additive set.pointwise_add_add_monoid._proof_2] pointwise_mul_monoid._proof_2
attribute [to_additive set.pointwise_add_add_monoid._proof_3] pointwise_mul_monoid._proof_3
attribute [to_additive set.pointwise_add_add_monoid] pointwise_mul_monoid

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
  by split; { rintros ⟨_, _, _, _, rfl⟩, rw mul_comm, exact ⟨_, ‹_›, _, ‹_›, rfl⟩ },
  ..pointwise_mul_semiring }

local attribute [instance] pointwise_mul_semiring

variables [monoid α] [monoid β] [is_monoid_hom f]

instance : is_semiring_hom (image f) :=
{ map_zero := image_empty _,
  map_one := by erw [image_singleton, is_monoid_hom.map_one f]; refl,
  map_add := image_union _,
  map_mul := λ s t, set.ext $ λ a,
  begin
    split,
    { rintros ⟨_, ⟨_, _, _, _, rfl⟩, rfl⟩,
      refine ⟨_, ⟨_, ‹_›, rfl⟩, _, ⟨_, ‹_›, rfl⟩, _⟩,
      apply is_monoid_hom.map_mul f },
    { rintros ⟨_, ⟨_, _, rfl⟩, _, ⟨_, _, rfl⟩, rfl⟩,
      refine ⟨_, ⟨_, ‹_›, _, ‹_›, rfl⟩, _⟩,
      apply is_monoid_hom.map_mul f }
  end }

end set
