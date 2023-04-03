/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice

/-!
# Relations holding pairwise on finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a few results about the interaction of `set.pairwise_disjoint` and `finset`,
as well as the interaction of `list.pairwise disjoint` and the condition of
`disjoint` on `list.to_finset`, in `set` form.
-/

open finset

variables {α ι ι' : Type*}

instance [decidable_eq α] {r : α → α → Prop} [decidable_rel r] {s : finset α} :
  decidable ((s : set α).pairwise r) :=
decidable_of_iff' (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) iff.rfl

lemma finset.pairwise_disjoint_range_singleton :
  (set.range (singleton : α → finset α)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

namespace set

lemma pairwise_disjoint.elim_finset {s : set ι} {f : ι → finset α}
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

namespace list
variables {β : Type*} [decidable_eq α] {r : α → α → Prop} {l : list α}

lemma pairwise_of_coe_to_finset_pairwise (hl : (l.to_finset : set α).pairwise r) (hn : l.nodup) :
  l.pairwise r :=
by { rw coe_to_finset at hl, exact hn.pairwise_of_set_pairwise hl }

lemma pairwise_iff_coe_to_finset_pairwise (hn : l.nodup) (hs : symmetric r) :
  (l.to_finset : set α).pairwise r ↔ l.pairwise r :=
by { rw [coe_to_finset, hn.pairwise_coe], exact ⟨hs⟩ }

lemma pairwise_disjoint_of_coe_to_finset_pairwise_disjoint {α ι}
  [semilattice_inf α] [order_bot α] [decidable_eq ι] {l : list ι} {f : ι → α}
  (hl : (l.to_finset : set ι).pairwise_disjoint f) (hn : l.nodup) :
  l.pairwise (_root_.disjoint on f) :=
pairwise_of_coe_to_finset_pairwise hl hn

lemma pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint {α ι}
  [semilattice_inf α] [order_bot α] [decidable_eq ι] {l : list ι} {f : ι → α} (hn : l.nodup) :
  (l.to_finset : set ι).pairwise_disjoint f ↔ l.pairwise (_root_.disjoint on f) :=
pairwise_iff_coe_to_finset_pairwise hn (symmetric_disjoint.comap f)

end list
