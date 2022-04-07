/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import order.partition.equipartition

/-!
# Equitabilising a partition

This file allows to blow partitions up into parts of controlled size. Given a partition `P` and
`a b m : ℕ`, we want to find a partition `Q` with `a` parts of size `m` and `b` parts of size
`m + 1` such that all parts of `P` are as close as possible to unions of parts of `Q`. Assuming the
ground set is of size `a * m + b * (m + 1)`, this is possible.

## Main declarations

* `finpartition.equitabilise`: `P.equitabilise h` where `h : a * m + b * (m + 1)` is a partition
  with `a` parts of size `m` and `b` parts of size `m + 1` which almost refines `P`.
* `finpartition.exists_dummy_equipartition`: We can find dummy equipartitions of arbitrary size.
-/

open finset nat

namespace finpartition
variables {α : Type*} [decidable_eq α] {s t : finset α} {m n a b : ℕ} {P : finpartition s}

lemma equitabilise_aux₀ (P : finpartition s) (hs : a * m + b * (m + 1) = s.card) (h : s = ∅) :
  ∃ Q : finpartition s,
    (∀ x : finset α, x ∈ Q.parts → x.card = m ∨ x.card = m + 1) ∧
    (∀ x, x ∈ P.parts → (x \ (Q.parts.filter $ λ y, y ⊆ x).bUnion id).card ≤ m) ∧
    (Q.parts.filter $ λ i, card i = m + 1).card = b :=
begin
  subst h,
  rw unique.eq_default P,
  refine ⟨finpartition.empty _, by simp, by simp, _⟩,
  simp only [card_empty, mul_eq_zero, succ_ne_zero, or_false, add_eq_zero_iff, and_false] at hs,
  simp [hs.2.symm],
end

lemma equitabilise_aux₁ (P : finset (finset α)) (hs : a * m + b * (m + 1) = s.card)
  (subs : ∀ i ∈ P, i ⊆ s) (h : m = 0) :
  ∃ Q : finpartition s,
    (∀ x : finset α, x ∈ Q.parts → x.card = m ∨ x.card = m + 1) ∧
    (∀ x, x ∈ P → (x \ (Q.parts.filter $ λ y, y ⊆ x).bUnion id).card ≤ m) ∧
    (Q.parts.filter $ λ i, card i = m + 1).card = b :=
begin
  subst h,
  simp only [mul_one, zero_add, mul_zero] at hs,
  simp only [exists_prop, card_eq_zero, zero_add, le_zero_iff, sdiff_eq_empty_iff_subset],
  refine ⟨⊥, by simp, λ x hx i hi, _, _⟩,
  { simp only [mem_bUnion, exists_prop, mem_filter, id.def, and_assoc],
    exact ⟨{i}, mem_map_of_mem _ (subs x hx hi), by simpa, by simp⟩ },
  { rw [filter_true_of_mem, card_bot, hs],
    simp }
end

lemma equitabilise_aux (P : finpartition s) (hs : a * m + b * (m + 1) = s.card) :
  ∃ Q : finpartition s,
    (∀ x : finset α, x ∈ Q.parts → x.card = m ∨ x.card = m + 1) ∧
    (∀ x, x ∈ P.parts → (x \ (Q.parts.filter $ λ y, y ⊆ x).bUnion id).card ≤ m) ∧
    (Q.parts.filter $ λ i, card i = m + 1).card = b :=
begin
  induction s using finset.strong_induction with s ih generalizing P a b,
  obtain hs' | hs' := eq_or_ne s ∅,
  { exact P.equitabilise_aux₀ hs hs' },
  cases m.eq_zero_or_pos with h m_pos,
  { exact equitabilise_aux₁ _ hs (λ i, P.le) h },
  have : 0 < a ∨ 0 < b,
  { simp_rw pos_iff_ne_zero,
    by_contra' h,
    simp only [h.1, h.2, add_zero, zero_mul, eq_comm, card_eq_zero] at hs,
    exact hs' hs },
  set t_size := if 0 < a then m else m + 1 with h',
  obtain ⟨ht₀, ht₁⟩ : 0 < t_size ∧ t_size ≤ m + 1,
  { rw h',
    split_ifs,
    { exact ⟨m_pos, le_succ _⟩ },
    { exact ⟨succ_pos', le_rfl⟩ } },
  by_cases ∃ u ∈ P.parts, m + 1 ≤ card u,
  { obtain ⟨u, hp₁, hp₂⟩ := h,
    obtain ⟨t, htu, ht₂⟩ := exists_smaller_set _ _ (ht₁.trans hp₂),
    have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = (s \ t).card,
    { rw [card_sdiff (htu.trans $ P.le hp₁), ←hs, ht₂, h'],
      split_ifs,
      { rw [tsub_mul, one_mul, tsub_add_eq_add_tsub (le_mul_of_pos_left h)] },
      { rw [tsub_mul, one_mul, ←add_tsub_assoc_of_le],
        exact le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left h) } },
    have : t.nonempty,
    { rwa [←card_pos, ht₂] },
    obtain ⟨R, hR₁, hR₂, hR₃⟩ :=
      @ih (s \ t) (sdiff_ssubset (htu.trans $ P.le hp₁) this) (P.avoid t)
        (if 0 < a then a-1 else a) (if 0 < a then b else b-1) hcard,
    refine ⟨R.extend this.ne_empty sdiff_disjoint (sdiff_sup_cancel $ htu.trans $ P.le hp₁),
      _, _, _⟩,
    { simp only [mem_insert, forall_eq_or_imp, extend_parts, and_iff_left hR₁, ht₂, h'],
      apply ite_eq_or_eq },
    { conv in (_ ∈ _) {rw ←insert_erase hp₁},
      simp only [and_imp, mem_insert, forall_eq_or_imp, ne.def, extend_parts],
      refine ⟨_, λ x hx, (card_le_of_subset _).trans $ hR₂ x _⟩,
      { simp only [filter_insert, if_pos htu, bUnion_insert, mem_erase, id.def],
        rcases eq_or_ne u t,
        { cases h.symm,
          rw sdiff_eq_empty_iff_subset.2 (subset_union_left _ _),
          exact m.zero_le },
        refine (card_le_of_subset $ λ i, _).trans (hR₂ (u \ t) _),
        { simp only [not_exists, mem_bUnion, and_imp, mem_union, mem_filter, mem_sdiff, id.def,
            not_or_distrib],
          intros hi₁ hi₂ hi₃,
          exact ⟨⟨hi₁, hi₂⟩, λ x hx hx', hi₃ _ hx (subset.trans hx' $ sdiff_subset _ _)⟩ },
        { simp only [avoid, sdiff_eq_empty_iff_subset, mem_image, exists_prop, of_erase, mem_erase,
            bot_eq_empty, ne.def],
          exact ⟨λ i, h (i.antisymm htu), _, hp₁, rfl⟩ } },
      { apply sdiff_subset_sdiff subset.rfl (bUnion_subset_bUnion_of_subset_left _ _),
        exact filter_subset_filter _ (subset_insert _ _) },
      { simp only [avoid, of_erase, mem_erase, mem_image, bot_eq_empty],
        refine ⟨(nonempty_of_mem_parts _ $ mem_of_mem_erase hx).ne_empty, _,
          mem_of_mem_erase hx, (disjoint_of_subset_right htu _).sdiff_eq_left⟩,
        exact P.disjoint (mem_of_mem_erase hx) hp₁ (ne_of_mem_erase hx) } },
    simp only [extend_parts, filter_insert, ht₂, h', one_ne_zero, ite_eq_right_iff,
      self_eq_add_right],
    split_ifs,
    { rw [card_insert_of_not_mem (λ ht, _), hR₃, if_neg h,
        nat.sub_add_cancel (‹0 < a ∨ 0 < b›.resolve_left h)],
      obtain ⟨i, hi⟩ := ‹t.nonempty›,
      exact (mem_sdiff.1 $ R.le (mem_filter.1 ht).1 hi).2 hi },
    { rw [hR₃, if_pos],
      simpa using h } },
  push_neg at h,
  have : t_size ≤ s.card,
  { rw [←hs, h'],
    split_ifs,
    { exact le_add_right (le_mul_of_pos_left ‹0 < a›) },
    { exact le_add_left (le_mul_of_pos_left $ ‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›) } },
  obtain ⟨s', hs'₁, hs'₂⟩ := exists_smaller_set _ _ this,
  have hs' : s'.nonempty,
  { rwa [←card_pos, hs'₂] },
  have : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = (s \ s').card,
  { rw [card_sdiff ‹s' ⊆ s›, hs'₂, h', ←hs],
    split_ifs,
    { rw [tsub_mul, one_mul,
        tsub_add_eq_add_tsub (le_mul_of_pos_left ‹0 < a›)] },
    { rw [tsub_mul, one_mul,
        ←add_tsub_assoc_of_le (le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›))] } },
  obtain ⟨R, hR₁, hR₂, hR₃⟩ := @ih (s \ s') (sdiff_ssubset hs'₁ ‹s'.nonempty›) (P.avoid s')
    (if 0 < a then a-1 else a) (if 0 < a then b else b-1) this,
  refine ⟨R.extend hs'.ne_empty sdiff_disjoint (sdiff_sup_cancel hs'₁), _, _, _⟩,
  { simp only [extend_parts, mem_insert, forall_eq_or_imp, and_iff_left hR₁, hs'₂, h'],
    exact ite_eq_or_eq _ _ _ },
  { refine λ x hx, (card_le_of_subset $ sdiff_subset _ _).trans _,
    rw ←lt_succ_iff,
    exact h _ hx },
  rw [extend_parts, filter_insert, hs'₂, h'],
  simp only [one_ne_zero, ite_eq_right_iff, self_eq_add_right],
  split_ifs,
  { rw [card_insert_of_not_mem, hR₃, if_neg h_1, tsub_add_cancel_of_le],
    { exact ‹0 < a ∨ 0 < b›.resolve_left h_1 },
    simp only [mem_filter, hs'₂, h', if_neg h_1, eq_self_iff_true, and_true],
    intro t,
    obtain ⟨i, hi⟩ := ‹s'.nonempty›,
    exact (mem_sdiff.1 $ R.le t hi).2 hi },
  { rw [hR₃, if_pos],
    simpa using h_1 }
end

/-- Given a partition `P` of `s`, as well as a proof that `a * m + b * (m + 1) = s.card`, build a
new partition `Q` of `s` where each part has size `m` or `m + 1`, every part of `P` is the union of
parts of `Q` plus at most `m` extra elements, there are `b` parts of size `m + 1` and (provided
`m > 0`, because a partition does not have parts of size `0`) there are `a` parts of size `m` and
hence `a + b` parts in total. -/
noncomputable def equitabilise (P : finpartition s) (h : a * m + b * (m + 1) = s.card) :
  finpartition s :=
(P.equitabilise_aux h).some

lemma card_eq_of_mem_parts_equitabilise (h : a * m + b * (m + 1) = s.card) :
  t ∈ (P.equitabilise h).parts → t.card = m ∨ t.card = m + 1 :=
(P.equitabilise_aux h).some_spec.1 _

lemma equitabilise_is_equipartition (P : finpartition s) (h : a * m + b * (m + 1) = s.card) :
  (P.equitabilise h).is_equipartition :=
set.equitable_on_iff_exists_eq_eq_add_one.2 ⟨m, λ u hu, card_eq_of_mem_parts_equitabilise h hu⟩

lemma card_filter_equitabilise_big (P : finpartition s) (h : a * m + b * (m + 1) = s.card) :
  ((P.equitabilise h).parts.filter $ λ u : finset α, u.card = m + 1).card = b :=
(P.equitabilise_aux h).some_spec.2.2

lemma card_filter_equitabilise_small (P : finpartition s) (hm : 0 < m)
  (h : a * m + b * (m + 1) = s.card) :
  ((P.equitabilise h).parts.filter $ λ u : finset α, u.card = m).card = a :=
begin
  refine (mul_eq_mul_right_iff.1 $ (add_left_inj (b * (m + 1))).1 _).resolve_right hm.ne',
  rw [h, ←(P.equitabilise h).sum_card_parts],
  have hunion : (P.equitabilise h).parts = (P.equitabilise h).parts.filter (λ u, u.card = m) ∪
    (P.equitabilise h).parts.filter (λ u, u.card = m + 1),
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_equitabilise h hx },
  nth_rewrite 1 hunion,
  rw [sum_union, sum_const_nat (λ x hx, (mem_filter.1 hx).2),
    sum_const_nat (λ x hx, (mem_filter.1 hx).2), P.card_filter_equitabilise_big],
  refine λ x hx, succ_ne_self m _,
  rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hx,
  rw [succ_eq_add_one, ←hx.2.2, hx.1.2],
end

lemma card_parts_equitabilise (hm : 0 < m) (h : a * m + b * (m + 1) = s.card) :
  (P.equitabilise h).parts.card = a + b :=
begin
  transitivity ((P.equitabilise h).parts.filter (λ u, u.card = m) ∪
    (P.equitabilise h).parts.filter (λ u, u.card = m + 1)).card,
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_equitabilise h hx },
  rw [card_union_eq, P.card_filter_equitabilise_small hm, P.card_filter_equitabilise_big],
  exact disjoint_filter.2 (λ x _ h₀ h₁, succ_ne_self m $ h₁.symm.trans h₀),
end

lemma card_parts_equitabilise_subset_le (h : a * m + b * (m + 1) = s.card) :
  t ∈ P.parts → (t \ ((P.equitabilise h).parts.filter $ λ u, u ⊆ t).bUnion id).card ≤ m :=
(classical.some_spec $ P.equitabilise_aux h).2.1 t

variables (s)

/-- An arbitrary equipartition into `n` parts. -/
lemma exists_dummy_equipartition (hn : 0 < n) (hs : n ≤ s.card) :
  ∃ P : finpartition s, P.is_equipartition ∧ P.parts.card = n :=
begin
  have : (n - s.card % n) * (s.card / n) + (s.card % n) * (s.card / n + 1) = s.card,
  { rw [tsub_mul, mul_add, ←add_assoc, tsub_add_cancel_of_le, mul_one, add_comm,
      mod_add_div],
    exact nat.mul_le_mul_right _ (mod_lt _ hn).le },
  refine ⟨(indiscrete (card_pos.1 $ hn.trans_le hs).ne_empty).equitabilise this,
    equitabilise_is_equipartition _ _, _⟩,
  rw [card_parts_equitabilise (nat.div_pos hs hn), tsub_add_cancel_of_le (mod_lt _ hn).le],
end

end finpartition
