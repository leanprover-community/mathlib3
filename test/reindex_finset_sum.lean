import algebra.big_operators
import data.nat.choose
import tactic.linarith

open finset

lemma choose_sum : Π (n : ℕ), (range (n + 1)).sum (λ m, choose n m) = 2^n
| 0 := by simp
| (n+1) :=
begin
  have h : ∀ x ∈ Ico 1 (n + 1), choose n ((x - 1) + 1) = choose n x,
  { intros x w,
    simp at w,
    replace w := w.left,
    congr,
    cases x, linarith, simp [add_comm], },

  calc
    (range (n + 2)).sum (λ m, choose (n + 1) m)
        = sum (Ico 0 (n + 2)) (λ (m : ℕ), choose (n + 1) m) : by rw ←Ico.zero_bot
    ... = choose (n + 1) 0 + sum (Ico 1 (n + 2)) (λ (m : ℕ), choose (n + 1) m) :
            by rw Ico_sum_split_first; linarith
    ... = choose (n + 1) 0 + sum (Ico 0 (n + 2 - 1)) (λ (x : ℕ), choose (n + 1) (x + 1)) :
            by rw Ico_sum_reindex_left 1; linarith
    ... = 1 + sum (Ico 0 (n + 1)) (λ (x : ℕ), choose n (x + 1) + choose n x) :
            by simp [choose_succ_succ]
    ... = 1 + (sum (Ico 0 (n + 1)) (λ (x : ℕ), choose n (x + 1))
            + sum (Ico 0 (n + 1)) (λ (x : ℕ), choose n x)) :
            by rw sum_add_distrib
    ... = 1 + (sum (Ico 1 (n + 2)) (λ (x : ℕ), choose n (x - 1 + 1))
            + sum (Ico 0 (n + 1)) (λ (x : ℕ), choose n x)) :
            by rw Ico_sum_reindex_right 1
    ... = 1 + (sum (Ico 1 (n + 1)) (λ (x : ℕ), choose n (x - 1 + 1))
            + sum (Ico 0 (n + 1)) (choose n)) :
            begin rw Ico_sum_split_last, simp, linarith end
    ... = 1 + (sum (Ico 1 (n + 1)) (λ (x : ℕ), choose n x)
            + sum (Ico 0 (n + 1)) (choose n)) :
            by rw sum_congr (eq.refl _) h
    ... = choose n 0 + (sum (Ico 1 (n + 1)) (λ (x : ℕ), choose n x)
            + sum (Ico 0 (n + 1)) (choose n)) :
            by conv { to_lhs, congr, rw ← choose_zero_right n }
    ... = sum (Ico 0 (n + 1)) (λ (x : ℕ), choose n x) + sum (Ico 0 (n + 1)) (λ (x : ℕ), choose n x) :
            by rw [←add_assoc, ←Ico_sum_split_first]; linarith; simp
    ... = 2^(n + 1) : by rw [Ico.zero_bot, choose_sum, nat.pow_succ]; ring
end
