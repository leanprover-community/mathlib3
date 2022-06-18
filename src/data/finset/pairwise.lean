/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice

/-!
# Relations holding pairwise on finite sets

In this file we prove a few results about the interaction of `set.pairwise_disjoint` and `finset`.
-/

open finset

variables {α ι ι' : Type*}

instance [decidable_eq α] {r : α → α → Prop} [decidable_rel r] {s : finset α} :
  decidable ((s : set α).pairwise r) :=
decidable_of_iff' (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) iff.rfl

lemma finset.pairwise_disjoint_range_singleton [decidable_eq α] :
  (set.range (singleton : α → finset α)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

namespace set

lemma pairwise_disjoint.elim_finset [decidable_eq α] {s : set ι} {f : ι → finset α}
  (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i)
  (haj : a ∈ f j) :
  i = j :=
hs.elim hi hj (finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

lemma pairwise_disjoint.image_finset_of_le [decidable_eq ι] [semilattice_inf α] [order_bot α]
  {s : finset ι} {f : ι → α} (hs : (s : set ι).pairwise_disjoint f) {g : ι → ι}
  (hf : ∀ a, f (g a) ≤ f a) :
  (s.image g : set ι).pairwise_disjoint f :=
begin
  rw coe_image,
  exact hs.image_of_le hf,
end

variables [lattice α] [order_bot α]

/-- Bind operation for `set.pairwise_disjoint`. In a complete lattice, you can use
`set.pairwise_disjoint.bUnion`. -/
lemma pairwise_disjoint.bUnion_finset {s : set ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.pairwise_disjoint (λ i' : ι', (g i').sup f))
  (hg : ∀ i ∈ s, (g i : set ι).pairwise_disjoint f) :
  (⋃ i ∈ s, ↑(g i)).pairwise_disjoint f :=
begin
  rintro a ha b hb hab,
  simp_rw set.mem_Union at ha hb,
  obtain ⟨c, hc, ha⟩ := ha,
  obtain ⟨d, hd, hb⟩ := hb,
  obtain hcd | hcd := eq_or_ne (g c) (g d),
  { exact hg d hd (by rwa hcd at ha) hb hab },
  { exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (finset.le_sup ha) (finset.le_sup hb) }
end

end set
