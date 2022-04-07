/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import algebra.order.with_zero
import order.partition.equipartition

/-!
# Constructions of `finpartition`
-/

open finpartition finset

variables {α : Type*}

section
variables [decidable_eq α] {s : finset α}

lemma equitabilise_aux1' {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finpartition s)
  (h : s = ∅) :
  ∃ (P : finpartition s),
    (∀ (x : finset α), x ∈ P.parts → x.card = m ∨ x.card = m + 1) ∧
    (∀ x, x ∈ A.parts → (x \ finset.bUnion (P.parts.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    ((P.parts.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  subst h,
  rw unique.eq_default A,
  refine ⟨finpartition.empty _, by simp, by simp, _⟩,
  simp only [finset.card_empty, nat.mul_eq_zero, nat.succ_ne_zero, or_false,
    add_eq_zero_iff, and_false] at hs,
  simp [hs.2.symm],
end

lemma equitabilise_aux2' {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
  (subs : ∀ i ∈ A, i ⊆ s) (h : m = 0) :
  ∃ (P : finpartition s),
    (∀ (x : finset α), x ∈ P.parts → x.card = m ∨ x.card = m+1) ∧
    (∀ x, x ∈ A → (x \ finset.bUnion (P.parts.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    ((P.parts.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  subst h,
  simp only [mul_one, zero_add, mul_zero] at hs,
  simp only [exists_prop, finset.card_eq_zero, zero_add, le_zero_iff, sdiff_eq_empty_iff_subset],
  refine ⟨⊥, by simp, λ x hx i hi, _, _⟩,
  { simp only [mem_bUnion, exists_prop, mem_filter, id.def, and_assoc],
    exact ⟨{i}, mem_map_of_mem _ (subs x hx hi), by simpa, by simp⟩ },
  { rw [filter_true_of_mem, card_bot, hs],
    simp }
end

lemma equitabilise_aux' {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finpartition s) :
  ∃ (P : finpartition s),
    (∀ (x : finset α), x ∈ P.parts → x.card = m ∨ x.card = m + 1) ∧
    (∀ x, x ∈ A.parts → (x \ finset.bUnion (P.parts.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    ((P.parts.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  induction s using finset.strong_induction with s ih generalizing A a b,
  cases s.eq_empty_or_nonempty with h hs_ne,
  { apply equitabilise_aux1' hs _ h },
  cases m.eq_zero_or_pos with h m_pos,
  { apply equitabilise_aux2' hs _ (λ i hi, A.le hi) h },
  have : 0 < a ∨ 0 < b,
  { by_contra,
    push_neg at h,
    simp only [le_zero_iff] at h,
    rw [h.1, h.2] at hs,
    simp only [add_zero, zero_mul, eq_comm, finset.card_eq_zero] at hs,
    exact hs_ne.ne_empty hs },
  set p'_size := if 0 < a then m else m+1 with h',
  have : 0 < p'_size,
  { rw h',
    split_ifs,
    { apply m_pos },
    exact nat.succ_pos' },
  by_cases ∃ p ∈ A.parts, m+1 ≤ finset.card p,
  { rcases h with ⟨p, hp₁, hp₂⟩,
    have : p'_size ≤ p.card,
    { apply le_trans _ hp₂,
      rw h',
      split_ifs,
      { apply nat.le_succ },
      refl },
    obtain ⟨p', hp'₁, hp'₂⟩ := exists_smaller_set _ _ this,
    have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = (s \ p').card,
    { rw [card_sdiff (hp'₁.trans (A.le hp₁)), ←hs, hp'₂, h'],
      split_ifs,
      { rw [nat.mul_sub_right_distrib, one_mul, tsub_add_eq_add_tsub (nat.le_mul_of_pos_left h)] },
      { rw [nat.mul_sub_right_distrib, one_mul, ←nat.add_sub_assoc],
        apply nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left h) } },
    have : p'.nonempty,
    { rwa [←card_pos, hp'₂] },
    obtain ⟨P', hP'₁, hP'₂, hP'₃⟩ :=
      @ih (s \ p') (sdiff_ssubset (hp'₁.trans (A.le hp₁)) this)
        (A.avoid p')
        (if 0 < a then a-1 else a)
        (if 0 < a then b else b-1)
        hcard,
    refine ⟨P'.extend this.ne_empty sdiff_disjoint (sdiff_sup_cancel $ hp'₁.trans $ A.le hp₁),
      _,  _, _⟩,
    { simp only [mem_insert, forall_eq_or_imp, extend_parts, and_iff_left hP'₁, hp'₂, h'],
      apply ite_eq_or_eq },
    { conv in (_ ∈ _) {rw ←finset.insert_erase hp₁},
      simp only [and_imp, mem_insert, forall_eq_or_imp, ne.def, extend_parts],
      split,
      { simp only [filter_insert, if_pos hp'₁, bUnion_insert, mem_erase, id.def],
        rcases eq_or_ne p p',
        { cases h.symm,
          rw sdiff_eq_empty_iff_subset.2,
          { simp },
          apply subset_union_left },
        apply le_trans (card_le_of_subset _) (hP'₂ (p \ p') _),
        { intros i,
          simp only [not_exists, mem_bUnion, and_imp, mem_union, mem_filter, mem_sdiff, id.def,
            not_or_distrib],
          intros hi₁ hi₂ hi₃,
          exact ⟨⟨hi₁, hi₂⟩, λ x hx hx', hi₃ _ hx (finset.subset.trans hx' (sdiff_subset _ _))⟩ },
        { simp only [avoid, sdiff_eq_empty_iff_subset, mem_image, exists_prop, of_erase, mem_erase,
            bot_eq_empty, ne.def],
          exact ⟨λ i, h (i.antisymm hp'₁), _, hp₁, rfl⟩ }},
      intros x hx,
      apply (card_le_of_subset _).trans (hP'₂ x _),
      { apply sdiff_subset_sdiff (finset.subset.refl _) (bUnion_subset_bUnion_of_subset_left _ _),
        refine filter_subset_filter _ (subset_insert _ _) },
      { simp only [avoid, of_erase, mem_erase, mem_image, bot_eq_empty],
        refine ⟨(nonempty_of_mem_parts _ (mem_of_mem_erase hx)).ne_empty, _,
          mem_of_mem_erase hx, _⟩,
        rw finset.sdiff_eq_self_iff_disjoint,
        refine disjoint.mono_right hp'₁ _,
        apply A.disjoint (mem_of_mem_erase hx) hp₁ (ne_of_mem_erase hx) } },
    simp only [extend_parts, filter_insert, hp'₂, h', nat.one_ne_zero, ite_eq_right_iff,
      self_eq_add_right],
    split_ifs,
    { rw [card_insert_of_not_mem, hP'₃, if_neg h, nat.sub_add_cancel],
      apply ‹0 < a ∨ 0 < b›.resolve_left h,
      simp only [mem_filter, hp'₂, h', if_neg h, eq_self_iff_true, and_true],
      intro t,
      obtain ⟨i, hi⟩ := ‹p'.nonempty›,
      apply (mem_sdiff.1 (P'.le t hi)).2 hi },
    { rw [hP'₃, if_pos],
      simpa using h } },
  push_neg at h,
  have : p'_size ≤ s.card,
  { rw [←hs, h'],
    split_ifs,
    { apply le_add_right (nat.le_mul_of_pos_left ‹0 < a›) },
    exact le_add_left (nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›)) },
  obtain ⟨s', hs'₁, hs'₂⟩ := exists_smaller_set _ _ this,
  have hs' : s'.nonempty,
  { rwa [←card_pos, hs'₂] },
  have : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = (s \ s').card,
  { rw [card_sdiff ‹s' ⊆ s›, hs'₂, h', ←hs],
    split_ifs,
    { rw [nat.mul_sub_right_distrib, one_mul,
        tsub_add_eq_add_tsub (nat.le_mul_of_pos_left ‹0 < a›)] },
    rw [nat.mul_sub_right_distrib, one_mul, ←nat.add_sub_assoc],
    exact nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›) },
  obtain ⟨P', hP'₁, hP'₂, hP'₃⟩ := @ih (s \ s') (sdiff_ssubset hs'₁ ‹s'.nonempty›) (A.avoid s')
    (if 0 < a then a-1 else a)
    (if 0 < a then b else b-1)
    this,
  refine ⟨P'.extend hs'.ne_empty sdiff_disjoint (sdiff_sup_cancel hs'₁), _, _, _⟩,
  { simp only [extend_parts, mem_insert, forall_eq_or_imp, and_iff_left hP'₁, hs'₂, h'],
    apply ite_eq_or_eq },
  { intros x hx,
    refine le_trans (card_le_of_subset (sdiff_subset _ _)) _,
    rw ←nat.lt_succ_iff,
    exact h _ hx },
  rw [extend_parts, filter_insert, hs'₂, h'],
  simp only [nat.one_ne_zero, ite_eq_right_iff, self_eq_add_right],
  split_ifs,
  { rw [card_insert_of_not_mem, hP'₃, if_neg h_1, nat.sub_add_cancel],
    { apply ‹0 < a ∨ 0 < b›.resolve_left h_1 },
    simp only [mem_filter, hs'₂, h', if_neg h_1, eq_self_iff_true, and_true],
    intro t,
    obtain ⟨i, hi⟩ := ‹s'.nonempty›,
    exact (mem_sdiff.1 (P'.le t hi)).2 hi },
  { rw [hP'₃, if_pos],
    simpa using h_1 }
end

/-! ### Equitabilise -/

namespace finpartition

/-- Given a partition `Q` of `s`, as well as a proof that `a*m + b*(m+1) = s.card`, build a new
partition `P` of `s` where each part has size `m` or `m+1`, every part of `Q` is the union of
parts of `P` plus at most `m` extra elements, there are `b` parts of size `m+1` and provided
`m > 0`, there are `a` parts of size `m` and hence `a+b` parts in total.
The `m > 0` condition is required since there may be zero or one parts of size `0`, while `a` could
be arbitrary. -/
noncomputable def equitabilise (Q : finpartition s) {m a b : ℕ} (h : a * m + b * (m + 1) = s.card) :
  finpartition s :=
(equitabilise_aux' h Q).some

lemma card_eq_of_mem_parts_equitabilise {Q : finpartition s} {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) {u : finset α} (hu : u ∈ (Q.equitabilise h).parts) :
  u.card = m ∨ u.card = m + 1 :=
(equitabilise_aux' h Q).some_spec.1 _ hu

lemma equitabilise.is_equipartition (Q : finpartition s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  (Q.equitabilise h).is_equipartition :=
set.equitable_on_iff_exists_eq_eq_add_one.2 ⟨m, λ u hu, card_eq_of_mem_parts_equitabilise h hu⟩

lemma card_filter_equitabilise_big (Q : finpartition s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  ((Q.equitabilise h).parts.filter (λ u : finset α, u.card = m + 1)).card = b :=
(equitabilise_aux' h Q).some_spec.2.2

lemma card_filter_equitabilise_small (Q : finpartition s) {m a b : ℕ} (hm : 0 < m)
  (h : a*m + b*(m+1) = s.card) :
  ((Q.equitabilise h).parts.filter (λ u : finset α, u.card = m)).card = a :=
begin
  refine (mul_eq_mul_right_iff.1 ((add_left_inj (b * (m + 1))).1 _)).resolve_right hm.ne',
  rw [h, ←(Q.equitabilise h).sum_card_parts],
  have hunion : (Q.equitabilise h).parts = (Q.equitabilise h).parts.filter (λ u, u.card = m) ∪
    (Q.equitabilise h).parts.filter (λ u, u.card = m + 1),
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_equitabilise h hx },
  nth_rewrite 1 hunion,
  rw [sum_union, sum_const_nat (λ x hx, (mem_filter.1 hx).2),
    sum_const_nat (λ x hx, (mem_filter.1 hx).2), Q.card_filter_equitabilise_big],
  refine λ x hx, nat.succ_ne_self m _,
  rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hx,
  rw [nat.succ_eq_add_one, ←hx.2.2, hx.1.2],
end

lemma equitabilise.parts_card {Q : finpartition s} {m a b : ℕ} (hm : 0 < m)
  (h : a * m + b * (m + 1) = s.card) :
  (Q.equitabilise h).parts.card = a + b :=
begin
  have hunion : (Q.equitabilise h).parts = (Q.equitabilise h).parts.filter (λ u, u.card = m) ∪
    (Q.equitabilise h).parts.filter (λ u, u.card = m + 1),
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_equitabilise h hx },
  rw [hunion, card_union_eq, Q.card_filter_equitabilise_small hm, Q.card_filter_equitabilise_big],
  refine λ x hx, nat.succ_ne_self m _,
  rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hx,
  rw [nat.succ_eq_add_one, ←hx.2.2, hx.1.2],
end

lemma almost_in_atoms_of_mem_parts_equitabilise {Q : finpartition s} {m a b : ℕ}
  (h : a * m + b * (m + 1) = s.card) {u : finset α} (hu : u ∈ Q.parts) :
  (u \ ((Q.equitabilise h).parts.filter $ λ x, x ⊆ u).bUnion id).card ≤ m :=
begin
  refine (card_le_of_subset _).trans ((classical.some_spec (equitabilise_aux' h Q)).2.1 u hu),
  intros x,
  simp only [not_exists, mem_bUnion, and_imp, mem_filter, mem_sdiff, id.def, ne.def],
  refine λ hxu hx, ⟨hxu, λ a ha hau, _⟩,
  obtain rfl | hanemp := eq_or_ne a ∅,
  { exact not_mem_empty _ },
  { apply hx _ ha hau },
end

end finpartition

end

/-! ### Atomise -/

open finpartition

section atomise
variables [decidable_eq α] {s : finset α}

lemma union_of_atoms_aux {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) (i : α) :
  (∃ (B ∈ (atomise s Q).parts), B ⊆ A ∧ i ∈ B) ↔ i ∈ A :=
begin
  split,
  { rintro ⟨B, hB₁, hB₂, hB₃⟩,
    exact hB₂ hB₃ },
  intro hi,
  obtain ⟨B, hB₁, hB₂⟩ := (atomise s Q).exists_mem (hs hi),
  refine ⟨B, hB₁, λ j hj, _, hB₂⟩,
  obtain ⟨P, hP, rfl⟩ := (mem_atomise.1 hB₁).2,
  simp only [mem_filter] at hB₂ hj,
  rwa [←hj.2 _ hA, hB₂.2 _ hA]
end

open_locale classical

lemma union_of_atoms' {Q : finset (finset α)} (A : finset α) (hx : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).parts.filter $ λ B, B ⊆ A ∧ B.nonempty).bUnion id = A :=
begin
  ext x,
  simp only [mem_bUnion, exists_prop, mem_filter, id.def, and_assoc],
  rw ←union_of_atoms_aux hx hs,
  simp only [exists_prop, finset.nonempty],
  tauto,
end

lemma partial_atomise {Q : finset (finset α)} (A : finset α) (hA : A ∈ Q) :
  ((atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty)).card ≤ 2^(Q.card - 1) :=
begin
  suffices h :
    (atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty) ⊆
      (Q.erase A).powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ insert A P ↔ i ∈ x)),
  { refine (card_le_of_subset h).trans (card_image_le.trans _),
    rw [card_powerset, card_erase_of_mem hA] },
  rw subset_iff,
  simp only [mem_erase, mem_sdiff, mem_powerset, mem_image, exists_prop, mem_filter, and_assoc,
    finset.nonempty, exists_imp_distrib, and_imp, mem_atomise, forall_apply_eq_imp_iff₂],
  rintro P' i hi P PQ rfl hy₂ j hj,
  refine ⟨P.erase A, erase_subset_erase _ PQ, _⟩,
  have : A ∈ P,
  { rw mem_filter at hi,
    rw hi.2 _ hA,
    exact hy₂ (mem_filter.2 hi) },
  simp only [insert_erase this, filter_congr_decidable],
end

end atomise

/-! ### Dummy -/

/-- Arbitrary equipartition into `t` parts -/
lemma dummy_equipartition [decidable_eq α] (s : finset α) {t : ℕ} (ht : 0 < t) (hs : t ≤ s.card) :
  ∃ (P : finpartition s), P.is_equipartition ∧ P.parts.card = t :=
begin
  have : (t - s.card % t) * (s.card / t) + (s.card % t) * (s.card / t + 1) = s.card,
  { rw [nat.mul_sub_right_distrib, mul_add, ←add_assoc, nat.sub_add_cancel, mul_one, add_comm,
      nat.mod_add_div],
    exact nat.mul_le_mul_right _ ((nat.mod_lt _ ht).le) },
  refine ⟨(finpartition.indiscrete (finset.card_pos.1 $ ht.trans_le hs).ne_empty).equitabilise this,
    equitabilise.is_equipartition _ _, _⟩,
  rw [equitabilise.parts_card (nat.div_pos hs ht), nat.sub_add_cancel (nat.mod_lt _ ht).le],
end
