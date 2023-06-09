/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.lattice
import data.set.pairwise.basic

/-!
# Relations holding pairwise

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove many facts about `pairwise` and the set lattice.
-/

open function set order

variables {α β γ ι ι' : Type*} {κ : Sort*} {r p q : α → α → Prop}

section pairwise
variables {f g : ι → α} {s t u : set α} {a b : α}

namespace set

lemma pairwise_Union {f : κ → set α} (h : directed (⊆) f) :
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
variables [complete_lattice α] {s : set ι} {t : set ι'}

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

lemma pairwise_disjoint.prod' {f : ι × ι' → α}
  (hs : s.pairwise_disjoint $ λ i, ⨆ i' ∈ t, f (i, i'))
  (ht : t.pairwise_disjoint $ λ i', ⨆ i ∈ s, f (i, i')) :
  (s ×ˢ t : set (ι × ι')).pairwise_disjoint f :=
begin
  rintro ⟨i, i'⟩ hi ⟨j, j'⟩ hj h,
  rw mem_prod at hi hj,
  obtain rfl | hij := eq_or_ne i j,
  { refine (ht hi.2 hj.2 $ (prod.mk.inj_left _).ne_iff.1 h).mono _ _,
    { convert le_supr₂ i hi.1, refl },
    { convert le_supr₂ i hj.1, refl } },
  { refine (hs hi.1 hj.1 hij).mono _ _,
    { convert le_supr₂ i' hi.2, refl },
    { convert le_supr₂ j' hj.2, refl } }
end

end complete_lattice

section frame
variables [frame α]

lemma pairwise_disjoint_prod_iff {s : set ι} {t : set ι'}
  {f : ι × ι' → α} :
  (s ×ˢ t : set (ι × ι')).pairwise_disjoint f ↔ s.pairwise_disjoint (λ i, ⨆ i' ∈ t, f (i, i')) ∧
    t.pairwise_disjoint (λ i', ⨆ i ∈ s, f (i, i')) :=
begin
  refine (⟨λ h, ⟨λ i hi j hj hij, _, λ i hi j hj hij, _⟩, λ h, h.1.prod' h.2⟩);
    simp_rw [function.on_fun, supr_disjoint_iff, disjoint_supr_iff]; intros i' hi' j' hj',
  { exact h (mk_mem_prod hi hi') (mk_mem_prod hj hj') (ne_of_apply_ne prod.fst hij) },
  { exact h (mk_mem_prod hi' hi) (mk_mem_prod hj' hj) (ne_of_apply_ne prod.snd hij) }
end

end frame

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

end set


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
