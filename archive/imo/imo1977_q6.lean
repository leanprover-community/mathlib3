/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
import data.pnat.basic

/-!
# IMO 1977 Q6

Suppose `f : ℕ+ → ℕ+` satisfies `f(f(n)) < f(n + 1)` for all `n`.
Prove that `f(n) = n` for all `n`.

We first prove the problem statement for `f : ℕ → ℕ`
then we use it to prove the statement for positive naturals.
-/

theorem imo1977_q6_nat (f : ℕ → ℕ) (h : ∀ n, f (f n) < f (n + 1)) :
  ∀ n, f n = n :=
begin
  have h' : ∀ (k n : ℕ), k ≤ n → k ≤ f n,
  { intro k,
    induction k with k h_ind,
    { intros, exact nat.zero_le _ },
    { intros n hk,
      apply nat.succ_le_of_lt,
      calc k ≤ f (f (n - 1)) : h_ind _ (h_ind (n - 1) (nat.le_sub_right_of_add_le hk))
         ... < f n           : nat.sub_add_cancel
        (le_trans (nat.succ_le_succ (nat.zero_le _)) hk) ▸ h _ } },
  have hf : ∀ n, n ≤ f n := λ n, h' n n rfl.le,
  have hf_mono : strict_mono f := strict_mono_nat_of_lt_succ (λ _, lt_of_le_of_lt (hf _) (h _)),
  intro,
  exact nat.eq_of_le_of_lt_succ (hf _) (hf_mono.lt_iff_lt.mp (h _))
end

theorem imo1977_q6 (f : ℕ+ → ℕ+) (h : ∀ n, f (f n) < f (n + 1)) :
  ∀ n, f n = n :=
begin
  intro n,
  simpa using imo1977_q6_nat (λ m, if 0 < m then f m.to_pnat' else 0) _ n,
  { intro x, cases x,
    { simp },
    { simpa using h _ } }
end
