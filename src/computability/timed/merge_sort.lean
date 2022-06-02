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
import computability.timed.split
import computability.timed.merge
/-!
# Timed Merge Sort
  This file defines a new version of Merge Sort that, besides sorting the input list, counts the
  number of operations made through the execution of the algorithm. Also, it presents proofs of
  it's time complexity and it's equivalence to the one defined in data/list/sort.lean
## Main Definition:
  - Timed.merge_sort : list α → (list α × ℕ)
## Main Results:
  - Timed.merge_sort_complexity :
      ∀ l : list α, (Timed.merge_sort r l).snd ≤ 8 * l.length * nat.log 2 l.length
  - Timed.merge_sort_equivalence :
      ∀ l : list α, (Timed.merge_sort r l).fst = list.merge_sort r l
     
-/

variables {α : Type} (r : α → α → Prop) [decidable_rel r]
local infix ` ≼ ` : 50 := r

namespace timed

include r

/-- Modified version of the merge sort algorithm, that also count
  the number of operations performed. -/
def merge_sort : list α → (list α × ℕ)
| []            := ([],  0)
| [a]           := ([a], 0)
| (a :: b :: l) := begin
  cases e : split (a :: b :: l) with l₁ l₂n,
  cases l₂n with l₂ n,
  cases length_split_lt e with h₁ h₂,
  have ms₁ := merge_sort l₁,
  have ms₂ := merge_sort l₂,
  have merged := merge r ms₁.fst ms₂.fst,
  have split_ops := (split (a :: b :: l)).snd.snd,
  exact (merged.fst , split_ops + ms₁.snd + ms₂.snd + merged.snd),
end
using_well_founded { rel_tac := λ_ _, `[exact ⟨_, inv_image.wf list.length nat.lt_wf⟩],
                     dec_tac := tactic.assumption }

theorem merge_sort_cons_cons_fst {a b n} {l l₁ l₂ : list α}
  (h : split (a :: b :: l) = (l₁, l₂, n)) :
  (merge_sort r (a :: b :: l)).fst = (merge r (merge_sort r l₁).fst (merge_sort r l₂).fst).fst :=
begin
  suffices : ∀ (L : list α × ℕ) h1, (@@and.rec
    (λ a a (_ : list.length l₁ < list.length l + 1 + 1 ∧
      list.length l₂ < list.length l + 1 + 1), L) h1 h1).fst = L.fst,
    { simp [merge_sort, h], apply this, },
  intros, cases h1, refl,
end

theorem merge_sort_equivalence : ∀ l : list α , (merge_sort r l).fst = list.merge_sort r l
| []       := by { unfold merge_sort, unfold list.merge_sort }
| [a]      := by { unfold merge_sort, unfold list.merge_sort }
| (a₁ :: a₂ :: t) :=
  have (split (a₁ :: a₂ :: t)).fst.length < (a₁ :: a₂ :: t).length :=
  begin
    cases e : split (a₁ :: a₂ :: t) with l₁ l₂n,
    cases l₂n with l₂ n,
    cases length_split_lt e with h₁ h₂,
    exact h₁,
  end,
  have (split (a₁ :: a₂ :: t)).snd.fst.length < (a₁ :: a₂ :: t).length :=
  begin
    cases e : split (a₁ :: a₂ :: t) with l₁ l₂n,
    cases l₂n with l₂ n,
    cases length_split_lt e with h₁ h₂,
    exact h₂,
  end,
begin
  rw list.merge_sort_cons_cons r (prod.ext rfl rfl),
  rw merge_sort_cons_cons_fst r (prod.ext rfl (prod.ext rfl rfl)),
  rw merge_equivalence,
  rw merge_sort_equivalence,
  rw merge_sort_equivalence,
  rw (split_equivalence (a₁ :: a₂ :: t)).left,
  rw (split_equivalence (a₁ :: a₂ :: t)).right,
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

theorem merge_sort_cons_cons_snd {a b n} {l l₁ l₂ : list α}
  (hs : split (a :: b :: l) = (l₁, l₂, n)) :
  (merge_sort r (a :: b :: l)).snd =
    (split (a :: b :: l)).snd.snd +
    (merge_sort r l₁).snd +
    (merge_sort r l₂).snd +
    (merge r (merge_sort r l₁).fst (merge_sort r l₂).fst).snd :=
begin
  suffices : ∀ (L : list α × ℕ) h1, (@@and.rec
    (λ a a (_ : list.length l₁ < list.length l + 1 + 1 ∧
      list.length l₂ < list.length l + 1 + 1), L) h1 h1).snd = L.snd,
    { simp [merge_sort, hs], apply this, },
  intros, cases h1, refl,
end

theorem merge_sort_complexity : ∀ l : list α,
  (merge_sort r l).snd ≤ 8 * l.length * nat.log 2 l.length
| []  := by { unfold merge_sort, simp only [nat.log_zero_right, list.length, mul_zero] }
| [a] := by { unfold merge_sort, simp only [nat.log_one_right, list.length_singleton, mul_zero] }
| (a₁ :: a₂ :: t) :=
let l := (a₁ :: a₂ :: t) in
begin
  rw merge_sort_cons_cons_snd r (prod.ext rfl (prod.ext rfl rfl)),
  rw split_complexity,
  cases hs : split l with l₁ l₂n,
  cases l₂n with l₂ n,
  have l₁_length : 2 * l₁.length ≤ l.length + 1 := (split_halves_length hs).1,
  have l₂_length : 2 * l₂.length ≤ l.length     := (split_halves_length hs).2,
  have l₂_length_half : l₂.length ≤ l.length / 2 := div_two l.length l₂.length l₂_length,
  have ih₁ := merge_sort_complexity l₁,
  have ih₂ := merge_sort_complexity l₂,
  have t_len_l_len : t.length + 2 = l.length := rfl,
  have l₁_length_weak : l₁.length ≤ l.length := by linarith,
  cases length_split_lt hs with hh₁ hh₂,
  cases h₁ : merge_sort r l₁ with l₁s ns,
  cases h₂ : merge_sort r l₂ with l₂s ms,

  have ms_bound : ms ≤ 4 * l.length * (nat.log 2 l.length - 1) :=
  begin
    have ms_id : (merge_sort r l₂).snd = ms := (congr_arg prod.snd h₂).trans rfl,
    rw ← ms_id,
    refine le_trans ih₂ _,
    rw log_pred l.length,
    calc 8 * l₂.length * nat.log 2 l₂.length
                = 4 * (2 * l₂.length) * nat.log 2 l₂.length :
                      by linarith
            ... ≤ 4 * l.length * nat.log 2 l₂.length :
                      begin
                        rw mul_assoc,
                        rw mul_assoc 4 l.length (nat.log 2 l₂.length),
                        refine (mul_le_mul_left zero_lt_four).mpr _,
                        exact nat.mul_le_mul_right (nat.log 2 l₂.length) l₂_length,
                      end
            ... ≤ 4 * l.length * nat.log 2 (l.length / 2) :
                      begin
                        refine nat.mul_le_mul_left (4 * l.length) _,
                        exact @nat.log_monotone 2 l₂.length (l.length / 2) l₂_length_half,
                      end
  end,

  have ns_bound : ns ≤ 4 * (l.length + 1) * nat.log 2 l.length :=
  begin
    have ns_id : (merge_sort r l₁).snd = ns := (congr_arg prod.snd h₁).trans rfl,
    rw ← ns_id,
    refine le_trans ih₁ _,
    calc 8 * l₁.length * nat.log 2 l₁.length
                = 4 * (2 * l₁.length) * nat.log 2 l₁.length :
                      by linarith
            ... ≤ 4 * (l.length + 1) * nat.log 2 l₁.length :
                      begin
                        rw mul_assoc,
                        rw mul_assoc 4 (l.length + 1) (nat.log 2 l₁.length),
                        refine (mul_le_mul_left zero_lt_four).mpr _,
                        exact nat.mul_le_mul_right (nat.log 2 l₁.length) l₁_length,
                      end
            ... ≤ 4 * (l.length + 1) * nat.log 2 l.length :
                      begin
                        refine nat.mul_le_mul_left (4 * (l.length + 1)) _,
                        exact @nat.log_monotone 2 l₁.length l.length l₁_length_weak,
                      end
  end,

  have split_length : l₁s.length + l₂s.length = l.length :=
  begin
    have l₁s_id : (merge_sort r l₁).fst = l₁s := (congr_arg prod.fst h₁).trans rfl,
    rw merge_sort_equivalence at l₁s_id,
    have same_lengths₁ := list.length_merge_sort r l₁,
    have l₁s_len_l₁_len : l₁s.length = l₁.length :=
    begin
      rw l₁s_id at same_lengths₁,
      exact same_lengths₁,
    end,

    have l₂s_id : (merge_sort r l₂).fst = l₂s := (congr_arg prod.fst h₂).trans rfl,
    rw merge_sort_equivalence at l₂s_id,
    have same_lengths₂ := list.length_merge_sort r l₂,
    have l₂s_len_l₂_len : l₂s.length = l₂.length :=
    begin
      rw l₂s_id at same_lengths₂,
      exact same_lengths₂,
    end,
    rw l₁s_len_l₁_len,
    rw l₂s_len_l₂_len,

    exact split_lengths l l₁ l₂ hs,
  end,

  simp only [list.length],
  rw t_len_l_len,

  have log_l_length : 1 ≤ nat.log 2 l.length :=
  begin
    calc 1 = nat.log 2 2 : log_2_val.symm
         ... ≤ nat.log 2 l.length : begin
                                      refine @nat.log_monotone 2 2 l.length _,
                                      linarith,
                                    end
  end,

  have four_log_l_length : 4 * 1 * l.length ≤ 4 * nat.log 2 l.length * l.length :=
  begin
    simp only [mul_le_mul_right, nat.succ_pos', mul_one, list.length],
    rw t_len_l_len,
    calc 4 = 4 * 1 : rfl
         ... ≤ 4 * nat.log 2 l.length : begin
                                          refine mul_le_mul' _ log_l_length,
                                          exact le_refl 4,
                                        end
  end,

  calc l.length + ns + ms + (merge r l₁s l₂s).snd
     ≤ l.length + ns + ms + (l₁s.length + l₂s.length) :
          add_le_add_left (merge_complexity r l₁s l₂s) (l.length + ns + ms)
 ... = l.length + ns + ms + l.length :
          congr_arg (has_add.add (list.length l + ns + ms)) split_length
 ... = 2 * l.length + ns + ms :
          by ring
 ... ≤ 2 * l.length + ns + 4 * l.length * (nat.log 2 l.length - 1) :
          begin
            refine add_le_add_left _ (2 * l.length + ns),
            exact ms_bound,
          end
 ... ≤ 2 * l.length + 4 * l.length * (nat.log 2 l.length - 1) + ns :
          by ring_nf
 ... ≤ 2 * l.length + 4 * l.length * (nat.log 2 l.length - 1) + 4 * (l.length + 1) *
       nat.log 2 l.length :
          begin
            refine add_le_add_left _ (2 * l.length + 4 * l.length * (nat.log 2 l.length - 1)),
            exact ns_bound,
          end
 ... ≤ 8 * l.length * nat.log 2 l.length :
          begin
            ring_nf,
            rw [ nat.mul_sub_left_distrib
               , add_mul
               , add_mul
               , nat.mul_sub_right_distrib
               ],
            refine (add_le_add_iff_left (4 * 1 * l.length)).mp _,
            rw [ ← add_assoc
               , ← add_assoc
               , ← add_assoc
               , ← nat.add_sub_assoc four_log_l_length (4 * 1 * l.length)
               , add_comm (4 * 1 * l.length) (4 * nat.log 2 l.length * l.length) 
               , nat.add_sub_assoc rfl.ge (4 * nat.log 2 l.length * l.length)
               , nat.sub_self (4 * 1 * l.length)
               ],
            simp only [add_zero, mul_one, list.length],
            rw t_len_l_len,
            ring_nf,
            rw [ add_mul
               , mul_assoc
               , mul_comm l.length (nat.log 2 l.length)
               , ← mul_assoc
               , add_assoc
               ],
            refine (add_le_add_iff_left (8 * nat.log 2 l.length * l.length)).mpr _,
            refine sum_2b (4 * nat.log 2 l.length) l.length _,
            rw ← t_len_l_len,
            have four_two_two: 4 = 2 * 2 := rfl,
            rw four_two_two,
            rw mul_assoc,
            refine mul_le_mul' (le_refl 2) _,
            exact log_2_times t.length,
          end,
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

end timed
