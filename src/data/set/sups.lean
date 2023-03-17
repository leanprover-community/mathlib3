/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.n_ary
import order.upper_lower.basic

/-!
# Set family operations

This file defines a few binary operations on `set α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.

## Notation

We define the following notation in locale `set_family`:
* `s ⊻ t`
* `s ⊼ t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

open function

variables {α : Type*}

/-- Notation typeclass for pointwise supremum `⊻`. -/
class has_sups (α : Type*) :=
(sups : α → α → α)

/-- Notation typeclass for pointwise infimum `⊼`. -/
class has_infs (α : Type*) :=
(infs : α → α → α)

-- This notation is meant to have higher precedence than `⊔` and `⊓`, but still within the realm of
-- other binary operations
infix ` ⊻ `:74 := has_sups.sups
infix ` ⊼ `:74 := has_infs.infs

namespace set
section sups
variables [semilattice_sup α] (s s₁ s₂ t t₁ t₂ u v : set α)

/-- `s ⊻ t` is the set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
protected def has_sups : has_sups (set α) := ⟨image2 (⊔)⟩

localized "attribute [instance] set.has_sups" in set_family

variables {s s₁ s₂ t t₁ t₂ u} {a b c : α}

@[simp] lemma mem_sups : c ∈ s ⊻ t ↔ ∃ (a ∈ s) (b ∈ t), a ⊔ b = c := by simp [(⊻)]

lemma sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t := mem_image2_of_mem
lemma sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ := image2_subset
lemma sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ := image2_subset_left
lemma sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t := image2_subset_right

lemma image_subset_sups_left : b ∈ t → (λ a, a ⊔ b) '' s ⊆ s ⊻ t := image_subset_image2_left
lemma image_subset_sups_right : a ∈ s → (⊔) a '' t ⊆ s ⊻ t := image_subset_image2_right

lemma forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ (a ∈ s) (b ∈ t), p (a ⊔ b) :=
forall_image2_iff

@[simp] lemma sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a ⊔ b ∈ u := image2_subset_iff

@[simp] lemma sups_nonempty : (s ⊻ t).nonempty ↔ s.nonempty ∧ t.nonempty := image2_nonempty_iff

protected lemma nonempty.sups : s.nonempty → t.nonempty → (s ⊻ t).nonempty := nonempty.image2
lemma nonempty.of_sups_left : (s ⊻ t).nonempty → s.nonempty := nonempty.of_image2_left
lemma nonempty.of_sups_right : (s ⊻ t).nonempty → t.nonempty := nonempty.of_image2_right

@[simp] lemma empty_sups : ∅ ⊻ t = ∅ := image2_empty_left
@[simp] lemma sups_empty : s ⊻ ∅ = ∅ := image2_empty_right
@[simp] lemma sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[simp] lemma singleton_sups : {a} ⊻ t = t.image (λ b, a ⊔ b) := image2_singleton_left
@[simp] lemma sups_singleton : s ⊻ {b} = s.image (λ a, a ⊔ b) := image2_singleton_right

lemma singleton_sups_singleton : ({a} ⊻ {b} : set α) = {a ⊔ b} := image2_singleton

lemma sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t := image2_union_left
lemma sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ := image2_union_right

lemma sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t := image2_inter_subset_left
lemma sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ := image2_inter_subset_right

variables (s t u v)

lemma Union_image_sup_left : (⋃ a ∈ s, (⊔) a '' t) = s ⊻ t := Union_image_left _
lemma Union_image_sup_right : (⋃ b ∈ t, (⊔ b) '' s) = s ⊻ t := Union_image_right _

@[simp] lemma image_sup_prod (s t : set α) : (s ×ˢ t).image (uncurry (⊔)) = s ⊻ t :=
image_uncurry_prod _ _ _

lemma sups_assoc : (s ⊻ t) ⊻ u = s ⊻ (t ⊻ u) := image2_assoc $ λ _ _ _, sup_assoc
lemma sups_comm : s ⊻ t = t ⊻ s := image2_comm $ λ _ _, sup_comm
lemma sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) := image2_left_comm sup_left_comm
lemma sups_right_comm : (s ⊻ t) ⊻ u = (s ⊻ u) ⊻ t := image2_right_comm sup_right_comm
lemma sups_sups_sups_comm : (s ⊻ t) ⊻ (u ⊻ v) = (s ⊻ u) ⊻ (t ⊻ v) :=
image2_image2_image2_comm sup_sup_sup_comm

end sups

section infs
variables [semilattice_inf α] (s s₁ s₂ t t₁ t₂ u v : set α)

/-- `s ⊼ t` is the set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
protected def has_infs : has_infs (set α) := ⟨image2 (⊓)⟩

localized "attribute [instance] set.has_infs" in set_family

variables {s s₁ s₂ t t₁ t₂ u} {a b c : α}

@[simp] lemma mem_infs : c ∈ s ⊼ t ↔ ∃ (a ∈ s) (b ∈ t), a ⊓ b = c := by simp [(⊼)]

lemma inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t := mem_image2_of_mem
lemma infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ := image2_subset
lemma infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ := image2_subset_left
lemma infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t := image2_subset_right

lemma image_subset_infs_left : b ∈ t → (λ a, a ⊓ b) '' s ⊆ s ⊼ t := image_subset_image2_left
lemma image_subset_infs_right : a ∈ s → (⊓) a '' t ⊆ s ⊼ t := image_subset_image2_right

lemma forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ (a ∈ s) (b ∈ t), p (a ⊓ b) :=
forall_image2_iff

@[simp] lemma infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a ⊓ b ∈ u := image2_subset_iff

@[simp] lemma infs_nonempty : (s ⊼ t).nonempty ↔ s.nonempty ∧ t.nonempty := image2_nonempty_iff

protected lemma nonempty.infs : s.nonempty → t.nonempty → (s ⊼ t).nonempty := nonempty.image2
lemma nonempty.of_infs_left : (s ⊼ t).nonempty → s.nonempty := nonempty.of_image2_left
lemma nonempty.of_infs_right : (s ⊼ t).nonempty → t.nonempty := nonempty.of_image2_right

@[simp] lemma empty_infs : ∅ ⊼ t = ∅ := image2_empty_left
@[simp] lemma infs_empty : s ⊼ ∅ = ∅ := image2_empty_right
@[simp] lemma infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[simp] lemma singleton_infs : {a} ⊼ t = t.image (λ b, a ⊓ b) := image2_singleton_left
@[simp] lemma infs_singleton : s ⊼ {b} = s.image (λ a, a ⊓ b) := image2_singleton_right
lemma singleton_infs_singleton : ({a} ⊼ {b} : set α) = {a ⊓ b} := image2_singleton

lemma infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t := image2_union_left
lemma infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ := image2_union_right

lemma infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t := image2_inter_subset_left
lemma infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ := image2_inter_subset_right

variables (s t u v)

lemma Union_image_inf_left : (⋃ a ∈ s, (⊓) a '' t) = s ⊼ t := Union_image_left _
lemma Union_image_inf_right : (⋃ b ∈ t, (⊓ b) '' s) = s ⊼ t := Union_image_right _

@[simp] lemma image_inf_prod (s t : set α) : (s ×ˢ t).image (uncurry (⊓)) = s ⊼ t :=
image_uncurry_prod _ _ _

lemma infs_assoc : (s ⊼ t) ⊼ u = s ⊼ (t ⊼ u) := image2_assoc $ λ _ _ _, inf_assoc
lemma infs_comm : s ⊼ t = t ⊼ s := image2_comm $ λ _ _, inf_comm
lemma infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) := image2_left_comm inf_left_comm
lemma infs_right_comm : (s ⊼ t) ⊼ u = (s ⊼ u) ⊼ t := image2_right_comm inf_right_comm
lemma infs_infs_infs_comm : (s ⊼ t) ⊼ (u ⊼ v) = (s ⊼ u) ⊼ (t ⊼ v) :=
image2_image2_image2_comm inf_inf_inf_comm

end infs
end set

open_locale set_family

@[simp] lemma upper_closure_sups [semilattice_sup α] (s t : set α) :
  upper_closure (s ⊻ t) = upper_closure s ⊔ upper_closure t :=
begin
  ext a,
  simp only [set_like.mem_coe, mem_upper_closure, set.mem_sups, exists_and_distrib_left,
    exists_prop, upper_set.coe_sup, set.mem_inter_iff],
  split,
  { rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩,
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩ },
  { rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩,
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, sup_le hab hac⟩ }
end

@[simp] lemma lower_closure_infs [semilattice_inf α] (s t : set α) :
  lower_closure (s ⊼ t) = lower_closure s ⊓ lower_closure t :=
begin
  ext a,
  simp only [set_like.mem_coe, mem_lower_closure, set.mem_infs, exists_and_distrib_left,
    exists_prop, lower_set.coe_sup, set.mem_inter_iff],
  split,
  { rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩,
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩ },
  { rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩,
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, le_inf hab hac⟩ }
end
