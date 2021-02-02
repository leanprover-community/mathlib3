/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import algebra.big_operators.basic
import tactic.linarith

/-!
# Finset lemmas

This file defines a few useful lemmas we need to develop the class number.
TODO: merge thes into appropriate files in `data/finset/`.

-/

open_locale big_operators

namespace finset

lemma map_max' {α β : Type*} [linear_order α] [linear_order β]
  {f : α → β} (hf : monotone f) (s : finset α) (h : s.nonempty) :
  f (s.max' h) = (s.image f).max' (h.image f) :=
begin
  obtain mem := finset.max'_mem s h,
  refine le_antisymm
    (finset.le_max' _ _ (finset.mem_image.mpr ⟨_, mem, rfl⟩))
    (finset.max'_le _ _ _ (λ y hy, _)),
  obtain ⟨x, hx, rfl⟩ := finset.mem_image.mp hy,
  exact hf (finset.le_max' _ _ hx)
end

lemma max'_lt {α : Type*} [linear_order α] (s : finset α) (h : s.nonempty)
  {x : α} (hx : ∀ y ∈ s, y < x) :
  s.max' h < x :=
lt_of_le_of_ne
  (finset.max'_le _ h _ (λ y hy, le_of_lt (hx y hy)))
  (ne_of_lt (hx _ (s.max'_mem h)))

lemma exists_eq_insert_of_lt_card {α : Type*} [decidable_eq α] (n : ℕ) (s : finset α)
  (h : n < s.card) : ∃ (x : α) (t : finset α), s = insert x t ∧ n ≤ t.card :=
begin
  have : 0 < s.card := by linarith,
  obtain ⟨x, hx⟩ := card_pos.mp this,
  use [x, s.erase x, (insert_erase hx).symm],
  rw card_erase_of_mem hx,
  exact nat.le_pred_of_lt h
end

lemma nonempty_of_lt_card {α : Type*}
  (s : finset α) {n : ℕ} (hn : n < card s) :
  s.nonempty :=
card_pos.mp (by linarith)

lemma le_card_erase_of_lt {α : Type*} [decidable_eq α]
  (s : finset α) {n : ℕ} (hn : n < card s) {x} (hx : x ∈ s) :
  n ≤ (s.erase x).card :=
by { rw card_erase_of_mem hx, exact nat.le_pred_of_lt hn }

/-- `finset.to_vec` noncomputably gives a vector of `n` distinct elements in `s` -/
noncomputable def to_vec {α : Type*} [decidable_eq α] :
  ∀ (s : finset α) {n : ℕ} (hn : n ≤ card s), fin n → α
| s 0       hn i := fin_zero_elim i
| s (n + 1) hn i := let h : ∃ x, x ∈ s := nonempty_of_lt_card s hn
in @fin.cons _ (λ _, α) (classical.some h) ((s.erase (classical.some h)).to_vec
  (le_card_erase_of_lt s hn (classical.some_spec h))) i

/-- Auxiliary lemma for proving `to_vec_mem`. -/
lemma to_vec_zero_mem {α : Type*} [decidable_eq α]
  (s : finset α) {n : ℕ} (hn : n.succ ≤ card s) :
  to_vec s hn 0 ∈ s :=
let h : ∃ x, x ∈ s := nonempty_of_lt_card s hn
in show classical.some h ∈ s, from classical.some_spec h

lemma to_vec_succ {α : Type*} [decidable_eq α]
  (s : finset α) {n : ℕ} (hn : n.succ ≤ card s) (i : fin n) :
  to_vec s hn i.succ =
    to_vec (s.erase (to_vec s hn 0))
                  (le_card_erase_of_lt s hn (to_vec_zero_mem s hn))
                  i :=
by simp only [to_vec, fin.cons_succ, fin.cons_zero]

lemma to_vec_mem {α : Type*} [decidable_eq α] :
  ∀ (s : finset α) {n : ℕ} (hn : n ≤ card s) (i : fin n),
  to_vec s hn i ∈ s
| s 0       hn i := fin_zero_elim i
| s (n + 1) hn i := let h : ∃ x, x ∈ s := nonempty_of_lt_card s hn
in fin.cases
  (show classical.some h ∈ s, from classical.some_spec h)
  (λ i, by { rw to_vec_succ,
             exact erase_subset _ _ (to_vec_mem (erase _ _) _ i) })
  i

lemma to_vec_succ_ne_to_vec_zero {α : Type*} [decidable_eq α] :
  ∀ (s : finset α) {n : ℕ} (hn : n.succ ≤ card s) (i : fin n),
  to_vec s hn i.succ ≠ to_vec s hn 0
| s 0       hn i := fin_zero_elim i
| s (n + 1) hn i :=
by { rw to_vec_succ, exact ne_of_mem_erase (to_vec_mem _ _ _) }

lemma to_vec_injective {α : Type*} [decidable_eq α] :
  ∀ (s : finset α) {n : ℕ} (hn : n ≤ card s),
  function.injective (to_vec s hn) :=
begin
  intros s n hn a b,
  induction n with n ih generalizing s hn,
  { rcases a with ⟨_, ⟨⟩⟩ },
  { refine fin.cases _ (λ a, _) a; refine fin.cases _ (λ b, _) b; intro h,
    { refl },
    { have := (to_vec_succ_ne_to_vec_zero s hn b).symm,
      contradiction },
    { have := to_vec_succ_ne_to_vec_zero s hn a,
      contradiction },
    { rw [to_vec_succ, to_vec_succ] at h,
      rw ih (s.erase _) _ h } }
end

end finset
