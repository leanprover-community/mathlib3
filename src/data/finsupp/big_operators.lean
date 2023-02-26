/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.finsupp.defs
import data.finset.pairwise

/-!

# Sums of collections of finsupp, and their support

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file provides results about the `finsupp.support` of sums of collections of `finsupp`,
including sums of `list`, `multiset`, and `finset`.

The support of the sum is a subset of the union of the supports:
* `list.support_sum_subset`
* `multiset.support_sum_subset`
* `finset.support_sum_subset`

The support of the sum of pairwise disjoint finsupps is equal to the union of the supports
* `list.support_sum_eq`
* `multiset.support_sum_eq`
* `finset.support_sum_eq`

Member in the support of the indexed union over a collection iff
it is a member of the support of a member of the collection:
* `list.mem_foldr_sup_support_iff`
* `multiset.mem_sup_map_support_iff`
* `finset.mem_sup_support_iff`

-/

variables {ι M : Type*} [decidable_eq ι]

lemma list.support_sum_subset [add_monoid M] (l : list (ι →₀ M)) :
  l.sum.support ⊆ l.foldr ((⊔) ∘ finsupp.support) ∅ :=
begin
  induction l with hd tl IH,
  { simp },
  { simp only [list.sum_cons, finset.union_comm],
    refine finsupp.support_add.trans (finset.union_subset_union _ IH),
    refl }
end

lemma multiset.support_sum_subset [add_comm_monoid M] (s : multiset (ι →₀ M)) :
  s.sum.support ⊆ (s.map (finsupp.support)).sup :=
begin
  induction s using quot.induction_on,
  simpa using list.support_sum_subset _
end

lemma finset.support_sum_subset [add_comm_monoid M] (s : finset (ι →₀ M)) :
  (s.sum id).support ⊆ finset.sup s finsupp.support :=
by { classical, convert multiset.support_sum_subset s.1; simp }

lemma list.mem_foldr_sup_support_iff [has_zero M] {l : list (ι →₀ M)} {x : ι} :
  x ∈ l.foldr ((⊔) ∘ finsupp.support) ∅ ↔ ∃ (f : ι →₀ M) (hf : f ∈ l), x ∈ f.support :=
begin
  simp only [finset.sup_eq_union, list.foldr_map, finsupp.mem_support_iff, exists_prop],
  induction l with hd tl IH,
  { simp },
  { simp only [IH, list.foldr_cons, finset.mem_union, finsupp.mem_support_iff, list.mem_cons_iff],
    split,
    { rintro (h|h),
      { exact ⟨hd, or.inl rfl, h⟩ },
      { exact h.imp (λ f hf, hf.imp_left or.inr) } },
    { rintro ⟨f, rfl|hf, h⟩,
      { exact or.inl h },
      { exact or.inr ⟨f, hf, h⟩ } } }
end

lemma multiset.mem_sup_map_support_iff [has_zero M] {s : multiset (ι →₀ M)} {x : ι} :
  x ∈ (s.map (finsupp.support)).sup ↔ ∃ (f : ι →₀ M) (hf : f ∈ s), x ∈ f.support :=
quot.induction_on s $ λ _, by simpa using list.mem_foldr_sup_support_iff

lemma finset.mem_sup_support_iff [has_zero M] {s : finset (ι →₀ M)} {x : ι} :
  x ∈ s.sup finsupp.support ↔ ∃ (f : ι →₀ M) (hf : f ∈ s), x ∈ f.support :=
multiset.mem_sup_map_support_iff

lemma list.support_sum_eq [add_monoid M] (l : list (ι →₀ M))
  (hl : l.pairwise (disjoint on finsupp.support)) :
  l.sum.support = l.foldr ((⊔) ∘ finsupp.support) ∅ :=
begin
  induction l with hd tl IH,
  { simp },
  { simp only [list.pairwise_cons] at hl,
    simp only [list.sum_cons, list.foldr_cons, function.comp_app],
    rw [finsupp.support_add_eq, IH hl.right, finset.sup_eq_union],
    suffices : disjoint hd.support (tl.foldr ((⊔) ∘ finsupp.support) ∅),
    { exact finset.disjoint_of_subset_right (list.support_sum_subset _) this },
    { rw [←list.foldr_map, ←finset.bot_eq_empty, list.foldr_sup_eq_sup_to_finset],
      rw finset.disjoint_sup_right,
      intros f hf,
      simp only [list.mem_to_finset, list.mem_map] at hf,
      obtain ⟨f, hf, rfl⟩ := hf,
      exact hl.left _ hf } }
end

lemma multiset.support_sum_eq [add_comm_monoid M] (s : multiset (ι →₀ M))
  (hs : s.pairwise (disjoint on finsupp.support)) :
  s.sum.support = (s.map finsupp.support).sup :=
begin
  induction s using quot.induction_on,
  obtain ⟨l, hl, hd⟩ := hs,
  convert list.support_sum_eq _ _,
  { simp },
  { simp },
  { simp only [multiset.quot_mk_to_coe'', multiset.coe_map, multiset.coe_eq_coe] at hl,
    exact hl.symm.pairwise hd (λ _ _ h, disjoint.symm h) }
end

lemma finset.support_sum_eq [add_comm_monoid M] (s : finset (ι →₀ M))
  (hs : (s : set (ι →₀ M)).pairwise_disjoint finsupp.support) :
  (s.sum id).support = finset.sup s finsupp.support :=
begin
  classical,
  convert multiset.support_sum_eq s.1 _,
  { exact (finset.sum_val _).symm },
  { obtain ⟨l, hl, hn⟩ : ∃ (l : list (ι →₀ M)), l.to_finset = s ∧ l.nodup,
    { refine ⟨s.to_list, _, finset.nodup_to_list _⟩,
      simp },
    subst hl,
    rwa [list.to_finset_val, list.dedup_eq_self.mpr hn,
        multiset.pairwise_coe_iff_pairwise,
        ←list.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint hn],
    intros x y hxy,
    exact symmetric_disjoint hxy }
end
