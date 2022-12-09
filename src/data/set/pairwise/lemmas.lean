/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.lattice
import data.set.pairwise.basic

/-!
# Relations holding pairwise

This file develops pairwise relations and defines pairwise disjoint indexed sets.

We also prove many basic facts about `pairwise`. It is possible that an intermediate file,
with more imports than `logic.pairwise` but not importing `data.set.lattice` would be appropriate
to hold many of these basic facts.

## Main declarations

* `set.pairwise_disjoint`: `s.pairwise_disjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `disjoint`.

## Notes

The spelling `s.pairwise_disjoint id` is preferred over `s.pairwise disjoint` to permit dot notation
on `set.pairwise_disjoint`, even though the latter unfolds to something nicer.
-/

open set function

variables {α β γ ι ι' : Type*} {r p q : α → α → Prop}

section pairwise
variables {f g : ι → α} {s t u : set α} {a b : α}

namespace set

lemma pairwise_Union {f : ι → set α} (h : directed (⊆) f) :
  (⋃ n, f n).pairwise r ↔ ∀ n, (f n).pairwise r :=
begin
  split,
  { assume H n,
    exact pairwise.mono (subset_Union _ _) H },
  { assume H i hi j hj hij,
    rcases mem_Union.1 hi with ⟨m, hm⟩,
    rcases mem_Union.1 hj with ⟨n, hn⟩,
    rcases h m n with ⟨p, mp, np⟩,
    exact H p (mp hm) (np hn) hij }
end

lemma pairwise_sUnion {r : α → α → Prop} {s : set (set α)} (h : directed_on (⊆) s) :
  (⋃₀ s).pairwise r ↔ (∀ a ∈ s, set.pairwise a r) :=
by { rw [sUnion_eq_Union, pairwise_Union (h.directed_coe), set_coe.forall], refl }

end set

end pairwise

namespace set
section partial_order_bot
variables [partial_order α] [order_bot α] {s t : set ι} {f g : ι → α}

lemma pairwise_disjoint_Union {g : ι' → set ι} (h : directed (⊆) g) :
  (⋃ n, g n).pairwise_disjoint f ↔ ∀ ⦃n⦄, (g n).pairwise_disjoint f :=
pairwise_Union h

lemma pairwise_disjoint_sUnion {s : set (set ι)} (h : directed_on (⊆) s) :
  (⋃₀ s).pairwise_disjoint f ↔ ∀ ⦃a⦄, a ∈ s → set.pairwise_disjoint a f :=
pairwise_sUnion h

end partial_order_bot

section complete_lattice
variables [complete_lattice α]

/-- Bind operation for `set.pairwise_disjoint`. If you want to only consider finsets of indices, you
can use `set.pairwise_disjoint.bUnion_finset`. -/
lemma pairwise_disjoint.bUnion {s : set ι'} {g : ι' → set ι} {f : ι → α}
  (hs : s.pairwise_disjoint (λ i' : ι', ⨆ i ∈ g i', f i))
  (hg : ∀ i ∈ s, (g i).pairwise_disjoint f) :
  (⋃ i ∈ s, g i).pairwise_disjoint f :=
begin
  rintro a ha b hb hab,
  simp_rw set.mem_Union at ha hb,
  obtain ⟨c, hc, ha⟩ := ha,
  obtain ⟨d, hd, hb⟩ := hb,
  obtain hcd | hcd := eq_or_ne (g c) (g d),
  { exact hg d hd (hcd.subst ha) hb hab },
  { exact (hs hc hd $ ne_of_apply_ne _ hcd).mono (le_supr₂ a ha) (le_supr₂ b hb) }
end

end complete_lattice

/-! ### Pairwise disjoint set of sets -/

lemma pairwise_disjoint_range_singleton :
  (set.range (singleton : ι → set ι)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

lemma pairwise_disjoint_fiber (f : ι → α) (s : set α) : s.pairwise_disjoint (λ a, f ⁻¹' {a}) :=
λ a _ b _ h, disjoint_iff_inf_le.mpr $ λ i ⟨hia, hib⟩, h $ (eq.symm hia).trans hib

-- classical
lemma pairwise_disjoint.elim_set {s : set ι} {f : ι → set α} (hs : s.pairwise_disjoint f) {i j : ι}
  (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
hs.elim hi hj $ not_disjoint_iff.2 ⟨a, hai, haj⟩

lemma bUnion_diff_bUnion_eq {s t : set ι} {f : ι → set α} (h : (s ∪ t).pairwise_disjoint f) :
  (⋃ i ∈ s, f i) \ (⋃ i ∈ t, f i) = (⋃ i ∈ s \ t, f i) :=
begin
  refine (bUnion_diff_bUnion_subset f s t).antisymm
    (Union₂_subset $ λ i hi a ha, (mem_diff _).2 ⟨mem_bUnion hi.1 ha, _⟩),
  rw mem_Union₂, rintro ⟨j, hj, haj⟩,
  exact (h (or.inl hi.1) (or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩,
end

/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def bUnion_eq_sigma_of_disjoint {s : set ι} {f : ι → set α}
  (h : s.pairwise_disjoint f) :
  (⋃ i ∈ s, f i) ≃ (Σ i : s, f i) :=
(equiv.set_congr (bUnion_eq_Union _ _)).trans $ Union_eq_sigma_of_disjoint $
  λ ⟨i, hi⟩ ⟨j, hj⟩ ne, h hi hj $ λ eq, ne $ subtype.eq eq

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
lemma pairwise_disjoint_image_right_iff {f : α → β → γ} {s : set α} {t : set β}
  (hf : ∀ a ∈ s, injective (f a)) :
  s.pairwise_disjoint (λ a, f a '' t) ↔ (s ×ˢ t).inj_on (λ p, f p.1 p.2) :=
begin
  refine ⟨λ hs x hx y hy (h : f _ _ = _), _, λ hs x hx y hy h, _⟩,
  { suffices : x.1 = y.1,
    { exact prod.ext this (hf _ hx.1 $ h.trans $ by rw this) },
    refine hs.elim hx.1 hy.1 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.2, _⟩),
    rw h,
    exact mem_image_of_mem _ hy.2 },
  { refine disjoint_iff_inf_le.mpr _,
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩,
    exact h (congr_arg prod.fst $ hs (mk_mem_prod hx ha) (mk_mem_prod hy hb) hab) }
end

/-- The partial images of a binary function `f` whose partial evaluations are injective are pairwise
disjoint iff `f` is injective . -/
lemma pairwise_disjoint_image_left_iff {f : α → β → γ} {s : set α} {t : set β}
  (hf : ∀ b ∈ t, injective (λ a, f a b)) :
  t.pairwise_disjoint (λ b, (λ a, f a b) '' s) ↔ (s ×ˢ t).inj_on (λ p, f p.1 p.2) :=
begin
  refine ⟨λ ht x hx y hy (h : f _ _ = _), _, λ ht x hx y hy h, _⟩,
  { suffices : x.2 = y.2,
    { exact prod.ext (hf _ hx.2 $ h.trans $ by rw this) this },
    refine ht.elim hx.2 hy.2 (not_disjoint_iff.2 ⟨_, mem_image_of_mem _ hx.1, _⟩),
    rw h,
    exact mem_image_of_mem _ hy.1 },
  { refine disjoint_iff_inf_le.mpr _,
    rintro _ ⟨⟨a, ha, hab⟩, b, hb, rfl⟩,
    exact h (congr_arg prod.snd $ ht (mk_mem_prod ha hx) (mk_mem_prod hb hy) hab) }
end

end set

lemma pairwise_disjoint_fiber (f : ι → α) : pairwise (disjoint on (λ a : α, f ⁻¹' {a})) :=
set.pairwise_univ.1 $ set.pairwise_disjoint_fiber f univ


section
variables {f : ι → set α} {s t : set ι}

lemma set.pairwise_disjoint.subset_of_bUnion_subset_bUnion (h₀ : (s ∪ t).pairwise_disjoint f)
  (h₁ : ∀ i ∈ s, (f i).nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) :
  s ⊆ t :=
begin
  rintro i hi,
  obtain ⟨a, hai⟩ := h₁ i hi,
  obtain ⟨j, hj, haj⟩ := mem_Union₂.1 (h $ mem_Union₂_of_mem hi hai),
  rwa h₀.eq (subset_union_left _ _ hi) (subset_union_right _ _ hj)
    (not_disjoint_iff.2 ⟨a, hai, haj⟩),
end

lemma pairwise.subset_of_bUnion_subset_bUnion (h₀ : pairwise (disjoint on f))
  (h₁ : ∀ i ∈ s, (f i).nonempty) (h : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, f i) :
  s ⊆ t :=
set.pairwise_disjoint.subset_of_bUnion_subset_bUnion (h₀.set_pairwise _) h₁ h

lemma pairwise.bUnion_injective (h₀ : pairwise (disjoint on f)) (h₁ : ∀ i, (f i).nonempty) :
  injective (λ s : set ι, ⋃ i ∈ s, f i) :=
λ s t h, (h₀.subset_of_bUnion_subset_bUnion (λ _ _, h₁ _) $ h.subset).antisymm $
  h₀.subset_of_bUnion_subset_bUnion (λ _ _, h₁ _) $ h.superset

end
