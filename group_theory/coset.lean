/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import group_theory.subgroup data.set.basic
open set function

variable {α : Type*}

def left_coset [has_mul α] (a : α) (s : set α) : set α := (λ x, a * x) '' s
def right_coset [has_mul α] (s : set α) (a : α) : set α := (λ x, x * a) '' s

local infix ` *l `:70 := left_coset
local infix ` *r `:70 := right_coset

section coset_mul
variable [has_mul α]

lemma mem_left_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
mem_image_of_mem (λ b : α, a * b) hxS

lemma mem_right_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
mem_image_of_mem (λ b : α, b * a) hxS

def left_coset_equiv (s : set α) (a b : α) := a *l s = b *l s

lemma left_coset_equiv_rel (s : set α) : equivalence (left_coset_equiv s) :=
mk_equivalence (left_coset_equiv s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup α]

@[simp] lemma left_coset_assoc (s : set α) (a b : α) : a *l (b *l s) = (a * b) *l s :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

@[simp] lemma right_coset_assoc (s : set α) (a b : α) : s *r a *r b = s *r (a * b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

lemma left_coset_right_coset (s : set α) (a b : α) : a *l s *r b = a *l (s *r b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

end coset_semigroup

section coset_monoid
variables [monoid α] (s : set α)

@[simp] lemma one_left_coset : 1 *l s = s :=
set.ext $ by simp [left_coset]

@[simp] lemma right_coset_one : s *r 1 = s :=
set.ext $ by simp [right_coset]

end coset_monoid

section coset_submonoid
open is_submonoid
variables [monoid α] (s : set α) [is_submonoid s]

lemma mem_own_left_coset (a : α) : a ∈ a *l s :=
suffices a * 1 ∈ a *l s, by simpa,
mem_left_coset a (one_mem s)

lemma mem_own_right_coset (a : α) : a ∈ s *r a :=
suffices 1 * a ∈ s *r a, by simpa,
mem_right_coset a (one_mem s)

lemma mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s :=
by rw [←ha]; exact mem_own_left_coset s a

lemma mem_right_coset_right_coset {a : α} (ha : s *r a = s) : a ∈ s :=
by rw [←ha]; exact mem_own_right_coset s a

end coset_submonoid

section coset_group
variables [group α] {s : set α} {x : α}

lemma mem_left_coset_iff (a : α) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨a⁻¹ * x, h, by simp⟩)

lemma mem_right_coset_iff (a : α) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨x * a⁻¹, h, by simp⟩)

end coset_group

section coset_subgroup
open is_submonoid
open is_subgroup
variables [group α] (s : set α) [is_subgroup s]

lemma left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
set.ext $ by simp [mem_left_coset_iff, mul_mem_cancel_right s (inv_mem ha)]

lemma right_coset_mem_right_coset {a : α} (ha : a ∈ s) : s *r a = s :=
set.ext $ assume b, by simp [mem_right_coset_iff, mul_mem_cancel_left s (inv_mem ha)]

theorem normal_of_eq_cosets [normal_subgroup s] (g : α) : g *l s = s *r g :=
set.ext $ assume a, by simp [mem_left_coset_iff, mem_right_coset_iff]; rw [mem_norm_comm_iff]

theorem eq_cosets_of_normal (h : ∀ g, g *l s = s *r g) : normal_subgroup s :=
⟨assume a ha g, show g * a * g⁻¹ ∈ s,
  by rw [← mem_right_coset_iff, ← h]; exact mem_left_coset g ha⟩

theorem normal_iff_eq_cosets : normal_subgroup s ↔ ∀ g, g *l s = s *r g :=
⟨@normal_of_eq_cosets _ _ s _, eq_cosets_of_normal s⟩

end coset_subgroup

def left_cosets [group α] (s : set α) : set (set α) := range (λa, a *l s)

namespace is_subgroup
open is_submonoid
variable [group α]

lemma subgroup_mem_left_cosets (s : set α) [is_subgroup s] : s ∈ left_cosets s :=
⟨1, by simp⟩

lemma left_cosets_disjoint {s : set α} [is_subgroup s] :
  ∀{s₁ s₂ : set α}, s₁ ∈ left_cosets s → s₂ ∈ left_cosets s → ∀{a}, a ∈ s₁ → a ∈ s₂ → s₁ = s₂
| _ _ ⟨a₁, rfl⟩ ⟨a₂, rfl⟩ a h₁ h₂ :=
  have h₁ : a₁⁻¹ * a ∈ s, by simpa [mem_left_coset_iff] using h₁,
  have h₂ : a₂⁻¹ * a ∈ s, by simpa [mem_left_coset_iff] using h₂,
  have a₁⁻¹ * a₂ ∈ s, by simpa [mul_assoc] using mul_mem h₁ (inv_mem h₂),
  have a₁ *l s = a₁ *l ((a₁⁻¹ * a₂) *l s), by rw [left_coset_mem_left_coset _ this],
  by simpa

lemma pairwise_left_cosets_disjoint {s : set α} (hs : is_subgroup s) :
  pairwise_on (left_cosets s) disjoint :=
assume s₁ h₁ s₂ h₂ ne, eq_empty_iff_forall_not_mem.mpr $ assume a ⟨ha₁, ha₂⟩,
  ne $ left_cosets_disjoint h₁ h₂ ha₁ ha₂

lemma left_cosets_equiv_subgroup {s : set α} (hs : is_subgroup s) :
  ∀{t : set α}, t ∈ left_cosets s → nonempty (t ≃ s)
| _ ⟨a, rfl⟩ := ⟨(equiv.set.image ((*) a) s injective_mul).symm⟩

lemma Union_left_cosets_eq_univ {s : set α} (hs : is_subgroup s) : ⋃₀ left_cosets s = univ :=
eq_univ_of_forall $ assume a, ⟨(*) a '' s, mem_range_self _, ⟨1, hs.one_mem, mul_one _⟩⟩

lemma group_equiv_left_cosets_times_subgroup {s : set α} (hs : is_subgroup s) :
  nonempty (α ≃ (left_cosets s × s)) :=
⟨calc α ≃ (@set.univ α) :
    (equiv.set.univ α).symm
  ... ≃ (⋃t∈left_cosets s, t) :
    by rw [←hs.Union_left_cosets_eq_univ]; simp
  ... ≃ (Σt:left_cosets s, t) :
    equiv.set.bUnion_eq_sigma_of_disjoint hs.pairwise_left_cosets_disjoint
  ... ≃ (Σt:left_cosets s, s) :
    equiv.sigma_congr_right $ λ⟨t, ht⟩, classical.choice $ hs.left_cosets_equiv_subgroup ht
  ... ≃ (left_cosets s × s) :
    equiv.sigma_equiv_prod _ _⟩

end is_subgroup
