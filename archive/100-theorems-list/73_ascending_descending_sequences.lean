/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.fintype.basic

/-!
# Erdos-Szekeres theorem

This file proves Theorem 73 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/),
also known as the Erdos-Szekeres theorem.

We use the proof outlined at
https://en.wikipedia.org/wiki/Erdos-Szekeres_theorem#Pigeonhole_principle

## Tags

sequences, increasing, decreasing, Ramsey, Erdos, Szekeres, Erdos-Szekeres, Erdős–Szekeres,
Erdős-Szekeres
-/


variables {α : Type*} [linear_order α] {β : Type*}

open function finset

def mono_inc_on [linear_order β] (f : α → β) (t : set α) := ∀ (x ∈ t) (y ∈ t), x < y → f x < f y
def mono_dec_on [linear_order β] (f : α → β) (t : set α) := ∀ (x ∈ t) (y ∈ t), x < y → f x > f y

lemma nat.succ_injective : injective nat.succ := λ x y, nat.succ_inj

lemma injective_of_lt_imp_ne (f : α → β) (h : ∀ x y, x < y → f x ≠ f y) : injective f :=
begin
  intros x y k,
  contrapose k,
  rw [←ne.def, ne_iff_lt_or_gt] at k,
  cases k,
  apply h _ _ k,
  rw eq_comm,
  apply h _ _ k,
end

lemma erdos_szekeres {r s n : ℕ} (f : fin n → α) (hn : r * s < n) (hf : injective f) :
  (∃ (t : finset (fin n)), r < t.card ∧ mono_inc_on f ↑t) ∨
  (∃ (t : finset (fin n)), s < t.card ∧ mono_dec_on f ↑t) :=
begin
  classical,
  let inc_sequences_ending_in : fin n → finset (finset (fin n)) :=
    λ i, univ.powerset.filter (λ t, finset.max t = some i ∧ mono_inc_on f ↑t),
  have inc_i : ∀ i, {i} ∈ inc_sequences_ending_in i := λ i, by simp [mono_inc_on],
  let dec_sequences_ending_in : fin n → finset (finset (fin n)) :=
    λ i, univ.powerset.filter (λ t, finset.max t = some i ∧ mono_dec_on f ↑t),
  have dec_i : ∀ i, {i} ∈ dec_sequences_ending_in i := λ i, by simp [mono_dec_on],
  let ab : fin n → ℕ × ℕ,
  { intro i,
    apply (max' ((inc_sequences_ending_in i).image card) (nonempty.image ⟨{i}, inc_i i⟩ _),
           max' ((dec_sequences_ending_in i).image card) (nonempty.image ⟨{i}, dec_i i⟩ _)) },
  have : injective ab,
  { apply injective_of_lt_imp_ne,
    intros i j k q,
    injection q with q₁ q₂,
    cases lt_or_gt_of_ne (λ _, ne_of_lt ‹i < j› (hf ‹f i = f j›)),
    work_on_goal 0 {apply ne_of_lt _ q₁}, work_on_goal 1 {apply ne_of_lt _ q₂},
    all_goals { rw nat.lt_iff_add_one_le, apply le_max' },
    work_on_goal 0 {have : (ab i).1 ∈ _ := max'_mem _ _},
    work_on_goal 1 {have : (ab i).2 ∈ _ := max'_mem _ _},
    all_goals
    { rw mem_image at this ⊢,
      rcases this with ⟨t, ht₁, ht₂⟩,
      rw mem_filter at ht₁,
      have : i ∈ t.max,
        simp [ht₁.2.1],
      refine ⟨insert j t, _, _⟩,
      swap,
      { rw [card_insert_of_not_mem, ht₂],
        intro _,
        apply not_le_of_lt ‹i < j›,
        apply le_max_of_mem ‹j ∈ t› ‹i ∈ t.max› },
      rw mem_filter,
      refine ⟨_, _, _⟩,
      { rw mem_powerset, apply subset_univ },
      { convert max_insert,
        rw [ht₁.2.1, option.lift_or_get_some_some, max_eq_left],
        refl,
        apply le_of_lt ‹i < j› },
      simp only [mono_inc_on, mono_dec_on, coe_insert, set.mem_insert_iff, mem_coe],
      rintros x ⟨rfl | _⟩ y ⟨rfl | _⟩ _,
      { apply (irrefl _ ‹j < j›).elim, },
      { exfalso,
        apply not_le_of_lt (trans ‹i < j› ‹j < y›) (le_max_of_mem ‹y ∈ t› ‹i ∈ t.max›) },
      { apply lt_of_le_of_lt _ ‹f i < f j› <|> apply lt_of_lt_of_le ‹f j < f i› _,
        rcases lt_or_eq_of_le (le_max_of_mem ‹x ∈ t› ‹i ∈ t.max›) with _ | rfl,
        { apply le_of_lt (ht₁.2.2 _ ‹x ∈ t› i (mem_of_max ‹ i ∈ t.max›) ‹x < i›) },
        { refl } },
      { apply ht₁.2.2 _ ‹x ∈ t› _ ‹y ∈ t› ‹x < y›} } },
  suffices : ∃ i, r < (ab i).1 ∨ s < (ab i).2,
  { obtain ⟨i, hi⟩ := this,
    apply or.imp _ _ hi,
    work_on_goal 0 {have : (ab i).1 ∈ _ := max'_mem _ _},
    work_on_goal 1 {have : (ab i).2 ∈ _ := max'_mem _ _},
    all_goals
    { intro hi,
      rw mem_image at this,
      obtain ⟨t, ht₁, ht₂⟩ := this,
      refine ⟨t, by rwa ht₂, _⟩,
      rw mem_filter at ht₁,
      apply ht₁.2.2 } },
  by_contra,
  push_neg at a,
  let ran : finset (ℕ × ℕ) := ((range r).image nat.succ).product ((range s).image nat.succ),
  have : image ab univ ⊆ ran,
  { rintro ⟨x₁, x₂⟩,
    simp only [mem_image, exists_prop, mem_range, mem_univ, mem_product, true_and, prod.mk.inj_iff],
    rintros ⟨i, rfl, rfl⟩,
    specialize a i,
    have z : 1 ≤ (ab i).1 ∧ 1 ≤ (ab i).2,
    { split;
      { apply le_max',
        rw mem_image,
        refine ⟨{i}, by solve_by_elim, card_singleton i⟩ } },
    refine ⟨_, _⟩,
    { refine ⟨(ab i).1 - 1, _, nat.succ_pred_eq_of_pos z.1⟩,
      rw nat.sub_lt_right_iff_lt_add z.1,
      apply nat.lt_succ_of_le a.1  },
    { refine ⟨(ab i).2 - 1, _, nat.succ_pred_eq_of_pos z.2⟩,
      rw nat.sub_lt_right_iff_lt_add z.2,
      apply nat.lt_succ_of_le a.2 } },
  apply not_le_of_lt hn,
  simpa [nat.succ_injective, card_image_of_injective, ‹injective ab›] using card_le_of_subset this,
end
