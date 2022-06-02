/-
Copyright (c) 2022 Tomaz Gomes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes
-/
import data.list.sort
import data.nat.log
import init.data.nat
import tactic.linarith

import computability.timed.lemmas
/-!
# Timed Split
  This file defines a new version of Split that, besides splitting the input lists into two halves,
  counts the number of operations made through the execution of the algorithm. Also, it presents
  proofs of it's time complexity, it's equivalence to the one defined in data/list/sort.lean and of
  some lemmas used in MergeSort.lean, related to the Split function.
## Main Definition
  - Timed.split : list α → (list α × list α × ℕ)
## Main Results
  - Timed.split_complexity :
      ∀ l : list α, (Timed.split l).snd.snd = l.length
  - Timed.split_equivalence :
      ∀ l : list α, (Timed.split l).fst = list.split l
-/

variables {α : Type}

namespace timed

/-- `split l` splits l into two lists, alternating the elements and
  count the number of recursive calls performed. -/
@[simp] def split : list α → (list α × list α × ℕ)
| []       := ([], [], 0)
| (h :: t) := let (l₁, l₂, n) := split t in (h :: l₂, l₁, n + 1)

theorem split_equivalence : ∀ (l : list α) ,
  (split l).fst = (list.split l).fst ∧ (split l).snd.fst = (list.split l).snd
| [] := by simp only [list.split, split, and_self]
| (h :: t) :=
begin
  simp only [list.split, split],

  have ih := split_equivalence t,
  cases ih with ih_fst ih_snd,

  cases (split t) with t_left₁ t_right₁,
  cases t_right₁ with t_right₁ _,
  unfold split,

  cases t.split with t_left₂ t_right₂,
  unfold list.split,
  simp only [true_and, eq_self_iff_true],

  exact ⟨ ih_snd, ih_fst ⟩,
end

theorem split_complexity : ∀ (l : list α) , (split l).snd.snd = l.length
| [] := by simp only [list.length, split]
| (h :: t) :=
begin
  simp only [list.length, split],
  have IH := split_complexity t,
  cases split t with l₁ l₂n,
  cases l₂n with l₂ n,
  unfold split,
  rw add_left_inj,
  exact IH,
end

lemma length_split_lt {a b: α} {l l₁ l₂ : list α} {n : ℕ}
  (h : split (a::b::l) = (l₁, l₂, n)):
    list.length l₁ < list.length (a::b::l) ∧
    list.length l₂ < list.length (a::b::l) :=
begin
  have split_eq_full : l₁ = (a::b::l).split.fst ∧ l₂ = (a::b::l).split.snd :=
  begin
    have l₂_n_id : (l₂, n) = (split (a :: b :: l)).snd :=
      (congr_arg prod.snd h).congr_right.mpr rfl,

    have l₂_id : l₂ = (split (a :: b :: l)).snd.fst :=
      (congr_arg prod.fst l₂_n_id).congr_right.mp rfl,

    have l₁_id : l₁ = (split (a :: b :: l)).fst :=
      (congr_arg prod.fst h).congr_right.mpr rfl,

    have split_eq := split_equivalence (a :: b :: l),
    cases split_eq,

    rw split_eq_left at l₁_id,
    rw split_eq_right at l₂_id,

    exact ⟨ l₁_id , l₂_id ⟩,
  end,
  cases split_eq_full,
  have reconstruct : (a::b::l).split = (l₁, l₂) :=
  begin
    rw split_eq_full_left,
    rw split_eq_full_right,
    exact prod.ext rfl rfl,
  end ,
  exact list.length_split_lt reconstruct,
end

lemma split_halves_length : ∀ {l l₁ l₂ : list α} {n : ℕ},
  split l = (l₁, l₂, n) → 
    2 * list.length l₁ ≤ list.length l + 1 ∧ 2 * list.length l₂ ≤ list.length l
| []       :=
begin
  intros l₁ l₂ n h,
  unfold split at h,
  simp only [prod.mk.inj_iff] at h,
  cases h  with h₁ h₂,
  cases h₂ with h₂ _,
  rw [← h₁, ← h₂],
  simp only [ zero_le_one
            , list.length
            , eq_self_iff_true
            , and_self
            , nonpos_iff_eq_zero
            , mul_zero
            ],
end
| (a :: t) :=
begin
  intros l₁ l₂ n h',
  cases e : split t with t₁ t₂m,
  cases t₂m with t₂ m,

  have split_id : split (a :: t) = (a :: t₂, t₁, m + 1) :=
  begin
    rw split,
    cases split t with t₁' t₂',
    cases t₂' with t₂' m₂,
    unfold split,
    injection e,
    injection h_2,
    refine congr (congr_arg prod.mk (congr_arg (list.cons a) h_3)) _,
    rw h_1,
    rw h_4,
  end,
  rw split_id at h',
  injection h',
  injection h_2,

  have IH := split_halves_length e,
  refine and.intro _ _,
  { rw ← h_1, simp only [list.length], linarith, },
  { rw ← h_3, simp only [list.length], linarith, },
end

lemma split_lengths : ∀ (l l₁ l₂ : list α) {n : ℕ},
  split l = (l₁, l₂, n) → l₁.length + l₂.length = l.length
| []  := by { intros l₁ l₂ n,
              simp only [ and_imp
                        , prod.mk.inj_iff
                        , list.length
                        , add_eq_zero_iff
                        , split
                        ],
              intros h₁ h₂ _,
              rw [← h₁, ← h₂],
              simp, }
| [a] := by { intros l₁ l₂ n,
              simp only [ and_imp
                        , prod.mk.inj_iff
                        , list.length_singleton
                        , zero_add
                        , split
                        ],
              intros h₁ h₂ _,
              rw [← h₁, ← h₂],
              simp only [list.length], }
| (a :: b :: t) :=
begin
  intros l₁ l₂ n h,
  cases e : split t with l₁' l₂'m,
  cases l₂'m with l₂' m,
  simp only [split] at h,
  rw e at h,
  unfold split at h,
  have ih := split_lengths t l₁' l₂' e,
  injection h,
  injection h_2,
  rw [← h_1, ← h_3],
  simp only [list.length], linarith,
end

end timed
