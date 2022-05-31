/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.basic
import order.upper_lower

/-!
# Intersecting families

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
section generalized_boolean_algebra
variables [generalized_boolean_algebra α] {s t : set α} {a b c : α}

/-- A set family is intersecting if every pair of elements is non-disjoint. -/
def intersecting (s : set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬ disjoint a b

lemma intersecting.mono (hs : s.intersecting) (h : t ⊆ s) : t.intersecting :=
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

end generalized_boolean_algebra

variables [boolean_algebra α]

lemma intersecting.not_compl_mem {s : set α} (hs : s.intersecting) {a : α} (ha : a ∈ s) : aᶜ ∉ s :=
λ h, hs ha h disjoint_compl_right

lemma intersecting.not_mem {s : set α} (hs : s.intersecting) {a : α} (ha : aᶜ ∈ s) : a ∉ s :=
λ h, hs ha h disjoint_compl_left

variables [fintype α] {s : finset α}

lemma intersecting.card_le (hs : (s : set α).intersecting) : 2 * s.card ≤ fintype.card α :=
begin
  classical,
  refine (s ∪ (s.map ⟨compl, compl_injective⟩)).card_le_univ.trans_eq' _,
  rw [two_mul, card_union_eq, card_map],
  rintro x hx,
  rw [finset.inf_eq_inter, finset.mem_inter, mem_map] at hx,
  obtain ⟨x, hx', rfl⟩ := hx.2,
  exact hs.not_compl_mem hx' hx.1,
end

variables [nontrivial α]

lemma intersecting.is_max_iff_card_eq (hs : (s : set α).intersecting) :
  (∀ t : finset α, (t : set α).intersecting → s ⊆ t → s = t) ↔ 2 * s.card = fintype.card α :=
begin
  classical,
  refine ⟨λ h, _, λ h t ht hst, eq_of_subset_of_card_le hst $
    le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) two_pos⟩,
  suffices : (s ∪ (s.map ⟨compl, compl_injective⟩)) = finset.univ,
  { rw [fintype.card, ←this, two_mul, card_union_eq, card_map],
    rintro x hx,
    rw [finset.inf_eq_inter, finset.mem_inter, mem_map] at hx,
    obtain ⟨x, hx', rfl⟩ := hx.2,
    exact hs.not_compl_mem hx' hx.1 },
  rw [←coe_eq_univ, coe_union, coe_map, function.embedding.coe_fn_mk,
    image_eq_preimage_of_inverse compl_compl compl_compl],
  refine eq_univ_of_forall (λ a, _),
  simp_rw [mem_union, mem_preimage],
  by_contra' ha,
  refine finset.ne_insert_of_not_mem _ _ ha.1 (h (insert a s) _ $ finset.subset_insert _ _),
  rw coe_insert,
  refine hs.insert _ (λ b hb hab, ha.2 $ (hs.is_upper_set' h) hab.le_compl' hb),
  rintro rfl,
  have := h {⊤} (by { rw coe_singleton, exact intersecting_singleton.2 top_ne_bot }),
  rw compl_bot at ha,
  rw coe_eq_empty.1 ((hs.is_upper_set' h).not_top_mem.1 ha.2) at this,
  exact singleton_ne_empty _ (this $ empty_subset _).symm,
end

lemma intersecting.exists_card_eq (hs : (s : set α).intersecting) :
  ∃ t, s ⊆ t ∧ 2 * t.card = fintype.card α ∧ (t : set α).intersecting :=
begin
  have := hs.card_le,
  rw [mul_comm, ←nat.le_div_iff_mul_le' two_pos] at this,
  revert hs,
  refine finset.strong_downward_induction_on s _ this,
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
