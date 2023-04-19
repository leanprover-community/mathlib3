/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.n_ary
import data.set.sups

/-!
# Set family operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a few binary operations on `finset α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
* `finset.disj_sups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a`
  and `b` are disjoint.

## Notation

We define the following notation in locale `finset_family`:
* `s ⊻ t`
* `s ⊼ t`
* `s ○ t` for `finset.disj_sups s t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

open function
open_locale set_family

variables {α : Type*} [decidable_eq α]

namespace finset
section sups
variables [semilattice_sup α] (s s₁ s₂ t t₁ t₂ u v : finset α)

/-- `s ⊻ t` is the finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
protected def has_sups : has_sups (finset α) := ⟨image₂ (⊔)⟩

localized "attribute [instance] finset.has_sups" in finset_family

variables {s t} {a b c : α}

@[simp] lemma mem_sups : c ∈ s ⊻ t ↔ ∃ (a ∈ s) (b ∈ t), a ⊔ b = c := by simp [(⊻)]

variables (s t)

@[simp, norm_cast] lemma coe_sups : (↑(s ⊻ t) : set α) = s ⊻ t := coe_image₂ _ _ _

lemma card_sups_le : (s ⊻ t).card ≤ s.card * t.card := card_image₂_le _ _ _

lemma card_sups_iff :
  (s ⊻ t).card = s.card * t.card ↔ (s ×ˢ t : set (α × α)).inj_on (λ x, x.1 ⊔ x.2) :=
card_image₂_iff

variables {s s₁ s₂ t t₁ t₂ u}

lemma sup_mem_sups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t := mem_image₂_of_mem
lemma sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ := image₂_subset
lemma sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ := image₂_subset_left
lemma sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t := image₂_subset_right

lemma image_subset_sups_left : b ∈ t → s.image (λ a, a ⊔ b) ⊆ s ⊻ t := image_subset_image₂_left
lemma image_subset_sups_right : a ∈ s → t.image ((⊔) a) ⊆ s ⊻ t := image_subset_image₂_right

lemma forall_sups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ (a ∈ s) (b ∈ t), p (a ⊔ b) :=
forall_image₂_iff

@[simp] lemma sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a ⊔ b ∈ u := image₂_subset_iff

@[simp] lemma sups_nonempty : (s ⊻ t).nonempty ↔ s.nonempty ∧ t.nonempty := image₂_nonempty_iff

protected lemma nonempty.sups : s.nonempty → t.nonempty → (s ⊻ t).nonempty := nonempty.image₂
lemma nonempty.of_sups_left : (s ⊻ t).nonempty → s.nonempty := nonempty.of_image₂_left
lemma nonempty.of_sups_right : (s ⊻ t).nonempty → t.nonempty := nonempty.of_image₂_right

@[simp] lemma empty_sups : ∅ ⊻ t = ∅ := image₂_empty_left
@[simp] lemma sups_empty : s ⊻ ∅ = ∅ := image₂_empty_right
@[simp] lemma sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[simp] lemma singleton_sups : {a} ⊻ t = t.image (λ b, a ⊔ b) := image₂_singleton_left
@[simp] lemma sups_singleton : s ⊻ {b} = s.image (λ a, a ⊔ b) := image₂_singleton_right

lemma singleton_sups_singleton : ({a} ⊻ {b} : finset α) = {a ⊔ b} := image₂_singleton

lemma sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t := image₂_union_left
lemma sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ := image₂_union_right

lemma sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t := image₂_inter_subset_left
lemma sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ := image₂_inter_subset_right

lemma subset_sups {s t : set α} :
  ↑u ⊆ s ⊻ t → ∃ s' t' : finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊻ t' :=
subset_image₂

variables (s t u v)

lemma bUnion_image_sup_left : s.bUnion (λ a, t.image $ (⊔) a) = s ⊻ t := bUnion_image_left
lemma bUnion_image_sup_right : t.bUnion (λ b, s.image $ λ a, a ⊔ b) = s ⊻ t := bUnion_image_right

@[simp] lemma image_sup_product (s t : finset α) : (s ×ˢ t).image (uncurry (⊔)) = s ⊻ t :=
image_uncurry_product _ _ _

lemma sups_assoc : (s ⊻ t) ⊻ u = s ⊻ (t ⊻ u) := image₂_assoc $ λ _ _ _, sup_assoc
lemma sups_comm : s ⊻ t = t ⊻ s := image₂_comm $ λ _ _, sup_comm
lemma sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) := image₂_left_comm sup_left_comm
lemma sups_right_comm : (s ⊻ t) ⊻ u = (s ⊻ u) ⊻ t := image₂_right_comm sup_right_comm
lemma sups_sups_sups_comm : (s ⊻ t) ⊻ (u ⊻ v) = (s ⊻ u) ⊻ (t ⊻ v) :=
image₂_image₂_image₂_comm sup_sup_sup_comm

end sups

section infs
variables [semilattice_inf α] (s s₁ s₂ t t₁ t₂ u v : finset α)

/-- `s ⊼ t` is the finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
protected def has_infs : has_infs (finset α) := ⟨image₂ (⊓)⟩

localized "attribute [instance] finset.has_infs" in finset_family

variables {s t} {a b c : α}

@[simp] lemma mem_infs : c ∈ s ⊼ t ↔ ∃ (a ∈ s) (b ∈ t), a ⊓ b = c := by simp [(⊼)]

variables (s t)

@[simp, norm_cast] lemma coe_infs : (↑(s ⊼ t) : set α) = s ⊼ t := coe_image₂ _ _ _

lemma card_infs_le : (s ⊼ t).card ≤ s.card * t.card := card_image₂_le _ _ _

lemma card_infs_iff :
  (s ⊼ t).card = s.card * t.card ↔ (s ×ˢ t : set (α × α)).inj_on (λ x, x.1 ⊓ x.2) :=
card_image₂_iff

variables {s s₁ s₂ t t₁ t₂ u}

lemma inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t := mem_image₂_of_mem
lemma infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ := image₂_subset
lemma infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ := image₂_subset_left
lemma infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t := image₂_subset_right

lemma image_subset_infs_left : b ∈ t → s.image (λ a, a ⊓ b) ⊆ s ⊼ t := image_subset_image₂_left
lemma image_subset_infs_right : a ∈ s → t.image ((⊓) a) ⊆ s ⊼ t := image_subset_image₂_right

lemma forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ (a ∈ s) (b ∈ t), p (a ⊓ b) :=
forall_image₂_iff

@[simp] lemma infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a ⊓ b ∈ u := image₂_subset_iff

@[simp] lemma infs_nonempty : (s ⊼ t).nonempty ↔ s.nonempty ∧ t.nonempty := image₂_nonempty_iff

protected lemma nonempty.infs : s.nonempty → t.nonempty → (s ⊼ t).nonempty := nonempty.image₂
lemma nonempty.of_infs_left : (s ⊼ t).nonempty → s.nonempty := nonempty.of_image₂_left
lemma nonempty.of_infs_right : (s ⊼ t).nonempty → t.nonempty := nonempty.of_image₂_right

@[simp] lemma empty_infs : ∅ ⊼ t = ∅ := image₂_empty_left
@[simp] lemma infs_empty : s ⊼ ∅ = ∅ := image₂_empty_right
@[simp] lemma infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[simp] lemma singleton_infs : {a} ⊼ t = t.image (λ b, a ⊓ b) := image₂_singleton_left
@[simp] lemma infs_singleton : s ⊼ {b} = s.image (λ a, a ⊓ b) := image₂_singleton_right

lemma singleton_infs_singleton : ({a} ⊼ {b} : finset α) = {a ⊓ b} := image₂_singleton

lemma infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t := image₂_union_left
lemma infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ := image₂_union_right

lemma infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t := image₂_inter_subset_left
lemma infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ := image₂_inter_subset_right

lemma subset_infs {s t : set α} :
  ↑u ⊆ s ⊼ t → ∃ s' t' : finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊼ t' :=
subset_image₂

variables (s t u v)

lemma bUnion_image_inf_left : s.bUnion (λ a, t.image $ (⊓) a) = s ⊼ t := bUnion_image_left
lemma bUnion_image_inf_right : t.bUnion (λ b, s.image $ λ a, a ⊓ b) = s ⊼ t := bUnion_image_right

@[simp] lemma image_inf_product (s t : finset α) : (s ×ˢ t).image (uncurry (⊓)) = s ⊼ t :=
image_uncurry_product _ _ _

lemma infs_assoc : (s ⊼ t) ⊼ u = s ⊼ (t ⊼ u) := image₂_assoc $ λ _ _ _, inf_assoc
lemma infs_comm : s ⊼ t = t ⊼ s := image₂_comm $ λ _ _, inf_comm
lemma infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) := image₂_left_comm inf_left_comm
lemma infs_right_comm : (s ⊼ t) ⊼ u = (s ⊼ u) ⊼ t := image₂_right_comm inf_right_comm
lemma infs_infs_infs_comm : (s ⊼ t) ⊼ (u ⊼ v) = (s ⊼ u) ⊼ (t ⊼ v) :=
image₂_image₂_image₂_comm inf_inf_inf_comm

end infs

open_locale finset_family

section distrib_lattice
variables [distrib_lattice α] (s t u : finset α)

lemma sups_infs_subset_left : s ⊻ (t ⊼ u) ⊆ (s ⊻ t) ⊼ (s ⊻ u) :=
image₂_distrib_subset_left $ λ _ _ _, sup_inf_left

lemma sups_infs_subset_right : (t ⊼ u) ⊻ s ⊆ (t ⊻ s) ⊼ (u ⊻ s) :=
image₂_distrib_subset_right $ λ _ _ _, sup_inf_right

lemma infs_sups_subset_left : s ⊼ (t ⊻ u) ⊆ (s ⊼ t) ⊻ (s ⊼ u) :=
image₂_distrib_subset_left $ λ _ _ _, inf_sup_left

lemma infs_sups_subset_right : (t ⊻ u) ⊼ s ⊆ (t ⊼ s) ⊻ (u ⊼ s) :=
image₂_distrib_subset_right $ λ _ _ _, inf_sup_right

end distrib_lattice

section disj_sups
variables [semilattice_sup α] [order_bot α] [@decidable_rel α disjoint]
  (s s₁ s₂ t t₁ t₂ u : finset α)

/-- The finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a` and `b` are disjoint.
-/
def disj_sups : finset α :=
((s ×ˢ t).filter $ λ ab : α × α, disjoint ab.1 ab.2).image $ λ ab, ab.1 ⊔ ab.2

localized "infix (name := finset.disj_sups) ` ○ `:74 := finset.disj_sups" in finset_family

variables {s t u} {a b c : α}

@[simp] lemma mem_disj_sups : c ∈ s ○ t ↔ ∃ (a ∈ s) (b ∈ t), disjoint a b ∧ a ⊔ b = c :=
by simp [disj_sups, and_assoc]

lemma disj_sups_subset_sups : s ○ t ⊆ s ⊻ t :=
begin
  simp_rw [subset_iff, mem_sups, mem_disj_sups],
  exact λ c ⟨a, b, ha, hb, h, hc⟩, ⟨a, b, ha, hb, hc⟩,
end

variables (s t)

lemma card_disj_sups_le : (s ○ t).card ≤ s.card * t.card :=
(card_le_of_subset disj_sups_subset_sups).trans $ card_sups_le _ _

variables {s s₁ s₂ t t₁ t₂ u}

lemma disj_sups_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ○ t₁ ⊆ s₂ ○ t₂ :=
image_subset_image $ filter_subset_filter _ $ product_subset_product hs ht

lemma disj_sups_subset_left (ht : t₁ ⊆ t₂) : s ○ t₁ ⊆ s ○ t₂ := disj_sups_subset subset.rfl ht
lemma disj_sups_subset_right (hs : s₁ ⊆ s₂) : s₁ ○ t ⊆ s₂ ○ t := disj_sups_subset hs subset.rfl

lemma forall_disj_sups_iff {p : α → Prop} :
  (∀ c ∈ s ○ t, p c) ↔ ∀ (a ∈ s) (b ∈ t), disjoint a b → p (a ⊔ b) :=
begin
  simp_rw mem_disj_sups,
  refine ⟨λ h a ha b hb hab, h _ ⟨_, ha, _, hb, hab, rfl⟩, _⟩,
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩,
  exact h _ ha _ hb hab,
end

@[simp] lemma disj_sups_subset_iff : s ○ t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), disjoint a b → a ⊔ b ∈ u :=
forall_disj_sups_iff

lemma nonempty.of_disj_sups_left : (s ○ t).nonempty → s.nonempty :=
by { simp_rw [finset.nonempty, mem_disj_sups], exact λ ⟨_, a, ha, _⟩, ⟨a, ha⟩ }

lemma nonempty.of_disj_sups_right : (s ○ t).nonempty → t.nonempty :=
by { simp_rw [finset.nonempty, mem_disj_sups], exact λ ⟨_, _, _, b, hb, _⟩, ⟨b, hb⟩ }

@[simp] lemma disj_sups_empty_left : ∅ ○ t = ∅ := by simp [disj_sups]
@[simp] lemma disj_sups_empty_right : s ○ ∅ = ∅ := by simp [disj_sups]

lemma disj_sups_singleton : ({a} ○ {b} : finset α) = if disjoint a b then {a ⊔ b} else ∅ :=
by split_ifs; simp [disj_sups, filter_singleton, h]

lemma disj_sups_union_left : (s₁ ∪ s₂) ○ t = s₁ ○ t ∪ s₂ ○ t :=
by simp [disj_sups, filter_union, image_union]
lemma disj_sups_union_right : s ○ (t₁ ∪ t₂) = s ○ t₁ ∪ s ○ t₂ :=
by simp [disj_sups, filter_union, image_union]

lemma disj_sups_inter_subset_left : (s₁ ∩ s₂) ○ t ⊆ s₁ ○ t ∩ s₂ ○ t :=
by simpa only [disj_sups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _
lemma disj_sups_inter_subset_right : s ○ (t₁ ∩ t₂) ⊆ s ○ t₁ ∩ s ○ t₂ :=
by simpa only [disj_sups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _

variables (s t)

lemma disj_sups_comm : s ○ t = t ○ s :=
by { ext, rw [mem_disj_sups, exists₂_comm], simp [sup_comm, disjoint.comm] }

end disj_sups

open_locale finset_family

section distrib_lattice
variables [distrib_lattice α] [order_bot α] [@decidable_rel α disjoint] (s t u v : finset α)

lemma disj_sups_assoc : ∀ s t u : finset α, (s ○ t) ○ u = s ○ (t ○ u) :=
begin
  refine associative_of_commutative_of_le disj_sups_comm _,
  simp only [le_eq_subset, disj_sups_subset_iff, mem_disj_sups],
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc,
  rw disjoint_sup_left at habc,
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, sup_assoc.symm⟩,
end

lemma disj_sups_left_comm : s ○ (t ○ u) = t ○ (s ○ u) :=
by simp_rw [←disj_sups_assoc, disj_sups_comm s]

lemma disj_sups_right_comm : (s ○ t) ○ u = (s ○ u) ○ t :=
by simp_rw [disj_sups_assoc, disj_sups_comm]

lemma disj_sups_disj_sups_disj_sups_comm : (s ○ t) ○ (u ○ v) = (s ○ u) ○ (t ○ v) :=
by simp_rw [←disj_sups_assoc, disj_sups_right_comm]

end distrib_lattice
end finset
