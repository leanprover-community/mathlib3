/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.card
import order.upper_lower.basic

/-!
# Intersecting families

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines intersecting families and proves their basic properties.

## Main declarations

* `set.intersecting`: Predicate for a set of elements in a generalized boolean algebra to be an
  intersecting family.
* `set.intersecting.card_le`: An intersecting family can only take up to half the elements, because
  `a` and `aᶜ` cannot simultaneously be in it.
* `set.intersecting.is_max_iff_card_eq`: Any maximal intersecting family takes up half the elements.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

open finset

variables {α : Type*}

namespace set
section semilattice_inf
variables [semilattice_inf α] [order_bot α] {s t : set α} {a b c : α}

/-- A set family is intersecting if every pair of elements is non-disjoint. -/
def intersecting (s : set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬ disjoint a b

@[mono] lemma intersecting.mono (h : t ⊆ s) (hs : s.intersecting) : t.intersecting :=
λ a ha b hb, hs (h ha) (h hb)

lemma intersecting.not_bot_mem (hs : s.intersecting) : ⊥ ∉ s := λ h, hs h h disjoint_bot_left

lemma intersecting.ne_bot (hs : s.intersecting) (ha : a ∈ s) : a ≠ ⊥ :=
ne_of_mem_of_not_mem ha hs.not_bot_mem

lemma intersecting_empty : (∅ : set α).intersecting := λ _, false.elim

@[simp] lemma intersecting_singleton : ({a} : set α).intersecting ↔ a ≠ ⊥ := by simp [intersecting]

lemma intersecting.insert (hs : s.intersecting) (ha : a ≠ ⊥) (h : ∀ b ∈ s, ¬ disjoint a b) :
  (insert a s).intersecting :=
begin
  rintro b (rfl | hb) c (rfl | hc),
  { rwa disjoint_self },
  { exact h _ hc },
  { exact λ H, h _ hb H.symm },
  { exact hs hb hc }
end

lemma intersecting_insert :
  (insert a s).intersecting ↔ s.intersecting ∧ a ≠ ⊥ ∧ ∀ b ∈ s, ¬ disjoint a b :=
⟨λ h, ⟨h.mono $ subset_insert _ _, h.ne_bot $ mem_insert _ _,
  λ b hb, h (mem_insert _ _) $ mem_insert_of_mem _ hb⟩, λ h, h.1.insert h.2.1 h.2.2⟩

lemma intersecting_iff_pairwise_not_disjoint :
  s.intersecting ↔ s.pairwise (λ a b, ¬ disjoint a b) ∧ s ≠ {⊥} :=
begin
  refine ⟨λ h, ⟨λ a ha b hb _, h ha hb, _⟩, λ h a ha b hb hab, _⟩,
  { rintro rfl,
    exact intersecting_singleton.1 h rfl },
  { have := h.1.eq ha hb (not_not.2 hab),
    rw [this, disjoint_self] at hab,
    rw hab at hb,
    exact h.2 (eq_singleton_iff_unique_mem.2
      ⟨hb, λ c hc, not_ne_iff.1 $ λ H, h.1 hb hc H.symm disjoint_bot_left⟩) }
end

protected lemma subsingleton.intersecting (hs : s.subsingleton) : s.intersecting ↔ s ≠ {⊥} :=
intersecting_iff_pairwise_not_disjoint.trans $ and_iff_right $ hs.pairwise _

lemma intersecting_iff_eq_empty_of_subsingleton [subsingleton α] (s : set α) :
  s.intersecting ↔ s = ∅ :=
begin
  refine subsingleton_of_subsingleton.intersecting.trans
    ⟨not_imp_comm.2 $ λ h, subsingleton_of_subsingleton.eq_singleton_of_mem _, _⟩,
  { obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 h,
    rwa subsingleton.elim ⊥ a },
  { rintro rfl,
    exact (set.singleton_nonempty _).ne_empty.symm }
end

/-- Maximal intersecting families are upper sets. -/
protected lemma intersecting.is_upper_set (hs : s.intersecting)
  (h : ∀ t : set α, t.intersecting → s ⊆ t → s = t) :
  is_upper_set s :=
begin
  classical,
  rintro a b hab ha,
  rw h (insert b s) _ (subset_insert _ _),
  { exact mem_insert _ _ },
  exact hs.insert (mt (eq_bot_mono hab) $ hs.ne_bot ha)
    (λ c hc hbc, hs ha hc $ hbc.mono_left hab),
end

/-- Maximal intersecting families are upper sets. Finset version. -/
lemma intersecting.is_upper_set' {s : finset α} (hs : (s : set α).intersecting)
  (h : ∀ t : finset α, (t : set α).intersecting → s ⊆ t → s = t) :
  is_upper_set (s : set α) :=
begin
  classical,
  rintro a b hab ha,
  rw h (insert b s) _ (finset.subset_insert _ _),
  { exact mem_insert_self _ _ },
  rw coe_insert,
  exact hs.insert (mt (eq_bot_mono hab) $ hs.ne_bot ha)
    (λ c hc hbc, hs ha hc $ hbc.mono_left hab),
end

end semilattice_inf

lemma intersecting.exists_mem_set {𝒜 : set (set α)} (h𝒜 : 𝒜.intersecting) {s t : set α}
  (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) : ∃ a, a ∈ s ∧ a ∈ t :=
not_disjoint_iff.1 $ h𝒜 hs ht

lemma intersecting.exists_mem_finset [decidable_eq α] {𝒜 : set (finset α)} (h𝒜 : 𝒜.intersecting)
  {s t : finset α} (hs : s ∈ 𝒜) (ht : t ∈ 𝒜) : ∃ a, a ∈ s ∧ a ∈ t :=
not_disjoint_iff.1 $ disjoint_coe.not.2 $ h𝒜 hs ht

variables [boolean_algebra α]

lemma intersecting.not_compl_mem {s : set α} (hs : s.intersecting) {a : α} (ha : a ∈ s) : aᶜ ∉ s :=
λ h, hs ha h disjoint_compl_right

lemma intersecting.not_mem {s : set α} (hs : s.intersecting) {a : α} (ha : aᶜ ∈ s) : a ∉ s :=
λ h, hs ha h disjoint_compl_left

lemma intersecting.disjoint_map_compl {s : finset α}
  (hs : (s : set α).intersecting) :
  disjoint s (s.map ⟨compl, compl_injective⟩) :=
begin
  rw finset.disjoint_left,
  rintro x hx hxc,
  obtain ⟨x, hx', rfl⟩ := mem_map.mp hxc,
  exact hs.not_compl_mem hx' hx,
end

lemma intersecting.card_le [fintype α] {s : finset α}
  (hs : (s : set α).intersecting) : 2 * s.card ≤ fintype.card α :=
begin
  classical,
  refine (s.disj_union _ hs.disjoint_map_compl).card_le_univ.trans_eq' _,
  rw [two_mul, card_disj_union, card_map],
end

variables [nontrivial α] [fintype α] {s : finset α}

-- Note, this lemma is false when `α` has exactly one element and boring when `α` is empty.
lemma intersecting.is_max_iff_card_eq (hs : (s : set α).intersecting) :
  (∀ t : finset α, (t : set α).intersecting → s ⊆ t → s = t) ↔ 2 * s.card = fintype.card α :=
begin
  classical,
  refine ⟨λ h, _, λ h t ht hst, finset.eq_of_subset_of_card_le hst $
    le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) two_pos⟩,
  suffices : s.disj_union (s.map ⟨compl, compl_injective⟩) (hs.disjoint_map_compl) = finset.univ,
  { rw [fintype.card, ←this, two_mul, card_disj_union, card_map] },
  rw [←coe_eq_univ, disj_union_eq_union, coe_union, coe_map, function.embedding.coe_fn_mk,
    image_eq_preimage_of_inverse compl_compl compl_compl],
  refine eq_univ_of_forall (λ a, _),
  simp_rw [mem_union, mem_preimage],
  by_contra' ha,
  refine s.ne_insert_of_not_mem _ ha.1 (h _ _ $ s.subset_insert _),
  rw coe_insert,
  refine hs.insert _ (λ b hb hab, ha.2 $ (hs.is_upper_set' h) hab.le_compl_left hb),
  rintro rfl,
  have := h {⊤} (by { rw coe_singleton, exact intersecting_singleton.2 top_ne_bot }),
  rw compl_bot at ha,
  rw coe_eq_empty.1 ((hs.is_upper_set' h).not_top_mem.1 ha.2) at this,
  exact finset.singleton_ne_empty _ (this $ empty_subset _).symm,
end

lemma intersecting.exists_card_eq (hs : (s : set α).intersecting) :
  ∃ t, s ⊆ t ∧ 2 * t.card = fintype.card α ∧ (t : set α).intersecting :=
begin
  have := hs.card_le,
  rw [mul_comm, ←nat.le_div_iff_mul_le' two_pos] at this,
  revert hs,
  refine s.strong_downward_induction_on _ this,
  rintro s ih hcard hs,
  by_cases ∀ t : finset α, (t : set α).intersecting → s ⊆ t → s = t,
  { exact ⟨s, subset.rfl, hs.is_max_iff_card_eq.1 h, hs⟩ },
  push_neg at h,
  obtain ⟨t, ht, hst⟩ := h,
  refine (ih _ (_root_.ssubset_iff_subset_ne.2 hst) ht).imp (λ u, and.imp_left hst.1.trans),
  rw [nat.le_div_iff_mul_le' two_pos, mul_comm],
  exact ht.card_le,
end

end set
