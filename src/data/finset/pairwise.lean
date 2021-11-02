/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.basic
import data.set.pairwise

/-!
# Relations holding pairwise on finite sets

In this file we prove a few results about `set_pairwise_disjoint s` for `s : finset α`.
-/

open finset

variables {α : Type*}

lemma finset.pairwise_disjoint_range_singleton [decidable_eq α] :
  (set.range (singleton : α → finset α)).pairwise_disjoint :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

lemma set.pairwise_disjoint.elim_finset [decidable_eq α] {s : set (finset α)}
  (hs : s.pairwise_disjoint) {x y : finset α} (hx : x ∈ s) (hy : y ∈ s) (z : α) (hzx : z ∈ x)
  (hzy : z ∈ y) : x = y :=
hs.elim hx hy (finset.not_disjoint_iff.2 ⟨z, hzx, hzy⟩)

lemma set.pairwise_disjoint.image_finset [decidable_eq α] [semilattice_inf_bot α]
  {s : finset α} (hs : (s : set α).pairwise_disjoint) {f : α → α} (hf : ∀ a, f a ≤ a) :
  set.pairwise_disjoint (s.image f :set α) :=
begin
  rw coe_image,
  exact hs.image_of_le hf,
end

lemma set.pairwise_disjoint_insert_finset [semilattice_inf_bot α] {s : finset α} {a : α} :
  (insert a s : set α).pairwise_disjoint ↔ (s : set α).pairwise_disjoint ∧
    ∀ b ∈ s, a ≠ b → disjoint a b :=
set.pairwise_insert_of_symmetric symmetric_disjoint

lemma set.pairwise_disjoint.insert_finset [semilattice_inf_bot α] {s : finset α}
  (hs : (s : set α).pairwise_disjoint) {a : α} (hx : ∀ b ∈ s, a ≠ b → disjoint a b) :
  (insert a s : set α).pairwise_disjoint :=
set.pairwise_disjoint_insert.2 ⟨hs, hx⟩
