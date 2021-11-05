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

variables {α ι : Type*}

lemma finset.pairwise_disjoint_range_singleton [decidable_eq α] :
  (set.range (singleton : α → finset α)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

lemma set.pairwise_disjoint.elim_finset [decidable_eq α] {s : set ι} {f : ι → finset α}
  (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i)
  (haj : a ∈ f j) :
  i = j :=
hs.elim hi hj (finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

lemma set.pairwise_disjoint.image_finset_of_le [decidable_eq ι] [semilattice_inf_bot α]
  {s : finset ι} {f : ι → α} (hs : (s : set ι).pairwise_disjoint f) {g : ι → ι}
  (hf : ∀ a, f (g a) ≤ f a) :
  (s.image g :set ι).pairwise_disjoint f :=
begin
  rw coe_image,
  exact hs.image_of_le hf,
end

lemma set.pairwise_disjoint_insert_finset [semilattice_inf_bot α] {s : finset ι} {f : ι → α}
  {a : ι} :
  (insert a s : set ι).pairwise_disjoint f ↔ (s : set ι).pairwise_disjoint f ∧
    ∀ b ∈ s, a ≠ b → disjoint (f a) (f b) :=
set.pairwise_insert_of_symmetric $ symmetric_disjoint.comap _

lemma set.pairwise_disjoint.insert_finset [semilattice_inf_bot α] {s : finset ι} {f : ι → α}
  (hs : (s : set ι).pairwise_disjoint f) {a : ι} (hx : ∀ b ∈ s, a ≠ b → disjoint (f a) (f b)) :
  (insert a s : set ι).pairwise_disjoint f :=
set.pairwise_disjoint_insert.2 ⟨hs, hx⟩
