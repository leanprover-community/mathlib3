/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.int.basic
import data.nat.fib
import tactic.linarith

/-!
# IMO 1981 Q3

Determine the maximum value of `m ^ 2 + n ^ 2`, where `m` and `n` are integers in
`{1, 2, ..., 1981}` and `(n ^ 2 - m * n - m ^ 2) ^ 2 = 1`.

The trick to this problem is that `m` and `n` have to be consecutive Fibonacci numbers,
because you can reduce any solution to a smaller one using the Fibonacci recurrence.
-/

/-
First, define the problem in terms of finding the maximum of a set.
-/

section
variable (N : ℕ) -- N = 1981

def in_range (n : ℤ) : Prop := 0 < n ∧ n ≤ N

def problem_predicate (m n : ℤ) : Prop :=
in_range N m ∧ in_range N n ∧ (n ^ 2 - m * n - m ^ 2) ^ 2 = 1

def specified_set : set ℤ :=
{k : ℤ | ∃ m : ℤ, ∃ n : ℤ, (k = m ^ 2 + n ^ 2 ∧ problem_predicate N m n)}

/-
We want to reduce every solution to a smaller solution. Specifically,
we show that when `(m, n)` is a solution, `(n - m, m)` is also a solution,
except for the base case of `(1, 1)`.
-/

lemma pp_m_le_n {m n : ℤ} (h1 : problem_predicate N m n) : m ≤ n :=
begin
  obtain (h2|h2) : m ≤ n ∨ ¬ m ≤ n, from em(m ≤ n),
  { exact h2 },
  { have h3 : n < m, from not_le.mp h2,
    unfold problem_predicate at h1,
    have h4 : n ^ 2 - m * n - m ^ 2 = n * (n - m) - m ^ 2, by ring,
    rw h4 at h1,
    have h5 : 0 < n, from h1.right.left.left,
    have h6 : n * (n - m) - m ^ 2 < -1, by nlinarith,
    have h7 : (n * (n - m) - m ^ 2) ^ 2 > 1, by nlinarith,
    exact absurd h1.right.right (ne_of_gt h7) }
end

lemma pp_eq_imp_1 {n : ℤ} (h1 : problem_predicate N n n) : n = 1 :=
begin
  have h2 : (n ^ 2 - n * n - n ^ 2) ^ 2 = 1, from h1.right.right,
  rw [pow_two, pow_two] at h2,
  norm_num at h2,
  have h3 : 0 < n, from h1.left.left,
  have h4 : 1 ≤ n, by linarith,
  obtain (h5|h5) : 1 = n ∨ 1 < n, from eq_or_lt_of_le h4,
  { exact h5.symm },
  { have h6 : 1 < n * n, by nlinarith,
    have h7 : 1 < n * n * (n * n), by nlinarith,
    exact absurd h2.symm (ne_of_lt h7) }
end

lemma pp_reduction {m n : ℤ} (h1 : problem_predicate N m n) (h2 : 1 < n) :
problem_predicate N (n - m) m :=
begin
  have h3 : (m ^ 2 - (n - m) * m - (n - m) ^ 2) ^ 2 = (n ^ 2 - m * n - m ^ 2) ^ 2, by ring,
  rw h1.right.right at h3,
  obtain (h4|h4) : m = n ∨ m < n, from eq_or_lt_of_le (pp_m_le_n N h1),
  { rw h4 at h1,
    have h5 : n = 1, from pp_eq_imp_1 N h1,
    exact absurd h5.symm (ne_of_lt h2) },
  have h6 : 0 < n - m, from sub_pos.mpr h4,
  have h7 : n - m < n, from sub_lt_self n h1.left.left,
  have h8 : n ≤ N, from h1.right.left.right,
  have h9 : n - m ≤ N, by linarith,
  exact ⟨⟨h6, h9⟩, ⟨h1.1, h3⟩⟩
end

/-
Now we can use induction to show that solutions must be Fibonacci numbers.
It will be convenient to have the lemmas above in their natural number form.
-/

def nat_predicate (m n : ℕ) : Prop := problem_predicate N ↑m ↑n

lemma np_m_le_n {m n : ℕ} (h1 : nat_predicate N m n) : m ≤ n :=
begin
  have h2 : ↑m ≤ ↑n, from pp_m_le_n N h1,
  norm_cast at h2,
  exact h2
end

lemma np_eq_imp_1 {n : ℕ} (h1 : nat_predicate N n n) : n = 1 :=
begin
  have h2 : ↑n = (1:ℤ), from pp_eq_imp_1 N h1,
  norm_cast at h2,
  exact h2
end

lemma np_reduction {m n : ℕ} (h1 : nat_predicate N m n) (h2 : 1 < n) :
  nat_predicate N (n - m) m :=
begin
  have h3 : (1:ℤ) < ↑ n, by {norm_cast, exact h2},
  unfold nat_predicate,
  have h4 : m ≤ n, from np_m_le_n N h1,
  have h5 : ↑(n - m) = ↑n - ↑m, from int.coe_nat_sub h4,
  rw h5,
  exact (pp_reduction N h1 h3)
end

lemma np_n_pos {m n : ℕ} (h1 : nat_predicate N m n) : 0 < n :=
begin
  have h2 : (0:ℤ) < ↑n, from h1.right.left.left,
  norm_cast at h2,
  exact h2
end

lemma np_m_pos {m n : ℕ} (h1 : nat_predicate N m n) : 0 < m :=
by exact_mod_cast h1.1.1

lemma np_n_le_N {m n : ℕ} (h1 : nat_predicate N m n) : n ≤ N :=
by exact_mod_cast h1.2.1.2

lemma np_imp_fib {n : ℕ} : ∀ m : ℕ, nat_predicate N m n →
  ∃ k : ℕ, m = k.fib ∧ n = (k + 1).fib :=
begin
  apply nat.strong_induction_on n _,
  intros n h1 m h2,
  have h3 : 0 < n, from np_n_pos N h2,
  have h4 : 0 < m, from np_m_pos N h2,
  have h5 : m ≤ n, from np_m_le_n N h2,
  obtain (h6|h6) : 1 = n ∨ 1 < n, from eq_or_lt_of_le (nat.succ_le_iff.mpr h3),
  { have h7 : 1 ≤ m, from nat.succ_le_iff.mpr h4,
    rw ← h6 at h5,
    have h8 : m = 1, from le_antisymm h5 h7,
    use 1,
    simp only [nat.fib_one, nat.fib_two],
    exact and.intro h8 h6.symm },
  { have h9 : nat_predicate N (n - m) m, from np_reduction N h2 h6,
    obtain (h10|h10) : m = n ∨ m < n, from eq_or_lt_of_le h5,
    { rw h10 at h2,
      exact absurd (np_eq_imp_1 N h2) (ne_of_gt h6) },
    { obtain ⟨k, h11⟩ : ∃ k : ℕ, (n - m) = k.fib ∧ m = (k+1).fib, from h1 m h10 (n - m) h9,
      use k + 1,
      split,
      { exact h11.right },
      { ring,
        rw [nat.fib_succ_succ, h11.left.symm, h11.right.symm],
        exact (nat.sub_eq_iff_eq_add h5).mp rfl } } }
end

lemma nat_abs_coe (n : ℤ) (h1 : 0 < n) : n = ↑(n.nat_abs) :=
begin
  obtain (h2|h2) : n = ↑(n.nat_abs) ∨ n = -↑(n.nat_abs), from int.nat_abs_eq n,
  { exact h2 },
  have h3 : 0 ≤ ↑(n.nat_abs), from zero_le ↑(int.nat_abs n),
  linarith
end

lemma coe_sq_le {m n: ℤ} (h1 : m.nat_abs ≤ n.nat_abs) : m ^ 2 ≤ n ^ 2 :=
begin
  rw [pow_two, pow_two],
  have h2 : m.nat_abs * m.nat_abs ≤ n.nat_abs * n.nat_abs, from nat.mul_le_mul h1 h1,
  rw [← int.nat_abs_mul_self, ← int.nat_abs_mul_self],
  norm_cast,
  exact h2
end

/-
Now we just have to demonstrate that 987 and 1597 are in fact the largest Fibonacci
numbers in this range, and thus provide the maximum of `specified_set`.
-/

variables {K : ℕ} (HK : N < K.fib + (K+1).fib) {N}
include HK

lemma m_n_bounds {m n : ℕ} (h1 : nat_predicate N m n) : m ≤ K.fib ∧ n ≤ (K+1).fib :=
begin
  obtain ⟨k, h2⟩ : ∃ k : ℕ, m = k.fib ∧ n = (k + 1).fib, from np_imp_fib N m h1,
  obtain (h3|h3) : k < K+1 ∨ ¬ k < K+1, from em(k < K+1),
  { have h4 : k ≤ K, from nat.lt_succ_iff.mp h3,
    have h5 : k.fib ≤ nat.fib K, from nat.fib_mono h4,
    have h6 : k + 1 ≤ K+1, from nat.succ_le_succ h4,
    have h7 : (k + 1).fib ≤ (K+1).fib, from nat.fib_mono h6,
    rw ← h2.left at h5,
    rw ← h2.right at h7,
    exact and.intro h5 h7 },
  { have h8 : K+1 ≤ k, from not_lt.mp h3,
    have h9 : K+2 ≤ k + 1, from nat.succ_le_succ h8,
    have h10 : (K+2).fib ≤ (k + 1).fib , from nat.fib_mono h9,
    norm_num [nat.fib_succ_succ] at h10,
    rw ← h2.right at h10,
    have h11 : n ≤ N, from np_n_le_N N h1,
    exact absurd (gt_of_ge_of_gt h10 HK) (not_lt.mpr h11) }
end

variables {M : ℕ} (HM : M = K.fib ^ 2 + (K+1).fib ^ 2)
include HM

lemma k_bound {m n : ℤ} (h2 : problem_predicate N m n) : m ^ 2 + n ^ 2 ≤ M :=
begin
  have h3 : 0 < m, from h2.left.left,
  have h4 : 0 < n, from h2.right.left.left,
  rw [nat_abs_coe m h3, nat_abs_coe n h4] at h2,
  have h7 : m.nat_abs ≤ K.fib ∧ n.nat_abs ≤ (K+1).fib, from m_n_bounds HK h2,
  have h8 : m ^ 2 ≤ K.fib ^ 2, from coe_sq_le h7.left,
  have h9 : n ^ 2 ≤ (K+1).fib ^ 2, from coe_sq_le h7.right,
  linarith
end

lemma solution_bound : ∀ {k : ℤ}, k ∈ specified_set N → k ≤ M
| _ ⟨m, n, rfl, h4⟩ := k_bound HK HM h4

theorem solution_greatest
  (H : problem_predicate N K.fib (K + 1).fib) : is_greatest (specified_set N) M :=
⟨⟨K.fib, (K+1).fib, by simp [HM], H⟩, λ k h1, solution_bound HK HM h1⟩

end

theorem imo1981_q3 : is_greatest (specified_set 1981) 3524578 :=
begin
  have := λ h, @solution_greatest 1981 16 h 3524578,
  simp only [
    show (16:ℕ).fib = 987 ∧ (16+1:ℕ).fib = 1597,
    by norm_num [nat.fib_succ_succ]] at this,
  norm_cast at this,
  apply this; norm_num [problem_predicate, in_range],
end
