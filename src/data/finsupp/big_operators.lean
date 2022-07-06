/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.finsupp.basic

/-!

# Sums of collections of finsupp, and their support

-/

variables {ι M : Type*} [decidable_eq ι]

open_locale big_operators

lemma list.support_sum_subset [add_monoid M] [decidable_eq (ι →₀ M)] (l : list (ι →₀ M)) :
  l.sum.support ⊆ finset.sup l.to_finset finsupp.support :=
begin
  induction l with hd tl IH,
  { simp },
  { simp only [list.sum_cons, list.to_finset_cons, finset.sup_insert, finset.sup_eq_union],
    refine finsupp.support_add.trans (finset.union_subset_union _ IH),
    refl }
end

lemma multiset.support_sum_subset [add_comm_monoid M] [decidable_eq (ι →₀ M)]
  (s : multiset (ι →₀ M)) :
  s.sum.support ⊆ finset.sup s.to_finset finsupp.support :=
begin
  induction s using quot.induction_on,
  simpa using list.support_sum_subset _
end

lemma finset.support_sum_subset [add_comm_monoid M]
  (s : finset (ι →₀ M)) :
  (s.sum id).support ⊆ finset.sup s finsupp.support :=
by { classical, convert multiset.support_sum_subset s.1; simp }

lemma list.mem_foldr_sup_support_iff [has_zero M] {l : list (ι →₀ M)} {x : ι} :
  x ∈ (l.map finsupp.support).foldr (⊔) ∅ ↔ ∃ (f : ι →₀ M) (hf : f ∈ l), x ∈ f.support :=
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

lemma multiset.mem_foldr_sup_support_iff [has_zero M] {s : multiset (ι →₀ M)} {x : ι} :
  x ∈ (s.map finsupp.support).fold (⊔) ∅ ↔ ∃ (f : ι →₀ M) (hf : f ∈ s), x ∈ f.support :=
quot.induction_on s $ λ _, list.mem_foldr_sup_support_iff

lemma finset.mem_sup_support_iff [has_zero M] {s : finset (ι →₀ M)} {x : ι} :
  x ∈ s.sup finsupp.support ↔ ∃ (f : ι →₀ M) (hf : f ∈ s), x ∈ f.support :=
multiset.mem_foldr_sup_support_iff

lemma list.support_sum_eq [add_monoid M] [decidable_eq (ι →₀ M)] (l : list (ι →₀ M))
  (hl : (l.map finsupp.support).pairwise disjoint) :
  l.sum.support = finset.sup l.to_finset finsupp.support :=
begin
  induction l with hd tl IH,
  { simp },
  { rw [list.map_cons, list.pairwise_cons] at hl,
    simp only [list.sum_cons, list.to_finset_cons, finset.sup_insert, finset.sup_eq_union],
    rw [finsupp.support_add_eq, IH hl.right],
    suffices : disjoint hd.support (tl.to_finset.sup finsupp.support),
    { exact finset.disjoint_of_subset_right (list.support_sum_subset _) this },
    { rw finset.disjoint_sup_right,
      intros f hf,
      simp only [ne.def, list.mem_to_finset, list.mem_filter] at hf,
      refine hl.left _ _,
      simp only [ne.def, list.mem_map, list.mem_filter],
      exact ⟨f, hf, rfl⟩ } }
end

lemma multiset.support_sum_eq [add_comm_monoid M] [decidable_eq (ι →₀ M)] (s : multiset (ι →₀ M))
  (hs : (s.map finsupp.support).pairwise disjoint) :
  s.sum.support = finset.sup s.to_finset finsupp.support :=
begin
  induction s using quot.induction_on,
  obtain ⟨l, hl, hd⟩ := hs,
  convert list.support_sum_eq _ _,
  { simp },
  { apply_instance },
  { simp only [multiset.quot_mk_to_coe'', multiset.coe_map, multiset.coe_eq_coe] at hl,
    exact hl.symm.pairwise hd disjoint.symm }
end

lemma list.pairwise_of_coe_to_finset_pairwise {α β} [decidable_eq α] {r : β → β → Prop}
  {f : α → β} {l : list α} (hl : (l.to_finset : set α).pairwise (r on f)) (hn : l.nodup) :
  l.pairwise (r on f) :=
begin
  induction l with hd tl IH,
  { simp },
  simp only [set.pairwise_insert, list.pairwise_cons, list.to_finset_cons, finset.coe_insert,
             finset.mem_coe, list.mem_to_finset, ne.def, list.nodup_cons] at hl hn ⊢,
  refine ⟨λ x hx, (hl.right x hx _).left, IH hl.left hn.right⟩,
  rintro rfl,
  exact hn.left hx
end

lemma list.pairwise_iff_coe_to_finset_pairwise {α β} [decidable_eq α] {r : β → β → Prop}
  {f : α → β} {l : list α} (hn : l.nodup) (hs : symmetric (r on f)):
  (l.to_finset : set α).pairwise (r on f) ↔ l.pairwise (r on f) :=
begin
  refine ⟨λ h, list.pairwise_of_coe_to_finset_pairwise h hn, λ h, _⟩,
  induction l with hd tl IH,
  { simp },
  simp only [set.pairwise_insert, list.to_finset_cons, finset.coe_insert, finset.mem_coe,
             list.mem_to_finset, ne.def, list.pairwise_cons, list.nodup_cons] at hn h ⊢,
  exact ⟨IH hn.right h.right, λ x hx hne, ⟨h.left _ hx, hs (h.left _ hx)⟩⟩
end

lemma list.pairwise_disjoint_of_coe_to_finset_pairwise_disjoint {α}
  [semilattice_inf α] [order_bot α] {l : list ι} {f : ι → α}
  (hl : (l.to_finset : set ι).pairwise_disjoint f) (hn : l.nodup) :
  l.pairwise (disjoint on f) :=
list.pairwise_of_coe_to_finset_pairwise hl hn

lemma list.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint {α}
  [semilattice_inf α] [order_bot α] {l : list ι} {f : ι → α} (hn : l.nodup) :
  (l.to_finset : set ι).pairwise_disjoint f ↔ l.pairwise (disjoint on f) :=
list.pairwise_iff_coe_to_finset_pairwise hn (symmetric_disjoint.comap f)

lemma finset.support_sum_eq [add_comm_monoid M] (s : finset (ι →₀ M))
  (hs : (s : set (ι →₀ M)).pairwise_disjoint finsupp.support) :
  (s.sum id).support = finset.sup s finsupp.support :=
begin
  classical,
  convert multiset.support_sum_eq s.1 _,
  { simp },
  { simp },
  { obtain ⟨l, hl, hn⟩ : ∃ (l : list (ι →₀ M)), l.to_finset = s ∧ l.nodup,
    { refine ⟨s.to_list, _, finset.nodup_to_list _⟩,
      simp },
    subst hl,
    simpa [list.dedup_eq_self.mpr hn, multiset.pairwise_coe_iff_pairwise symmetric_disjoint,
           list.pairwise_map, ←list.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint hn]
           using hs }
end
