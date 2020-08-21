/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.rat
import data.fintype.card

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of numbers that frequently show up in number theory.

For example, they show up in the Taylor series of many trigonometric and hyperbolic functions,
and also as (integral multiples of products of powers of `π` and)
special values of the Riemann zeta function.
(Note: these facts are not yet available in mathlib)

In this file, we provide the definition,
and the basic fact (`sum_bernoulli`) that
$$ \sum_{k < n} \binom{n}{k} * B_k = n, $$
where $B_k$ denotes the the $k$-th Bernoulli number.

-/

open_locale big_operators

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = \sum_{k < n} \binom{n}{k} * \frac{B_k}{n+1-k}$$ -/
def bernoulli : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - ∑ k : fin n, (n.choose k) * bernoulli k k.2 / (n + 1 - k))

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, (n.choose k) * (bernoulli k) / (n + 1 - k) :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, (n.choose k) * (bernoulli k) / (n + 1 - k) :=
by { rw [bernoulli_def', finset.range_sum_eq_univ_sum], refl }

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl
@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end

@[simp] lemma sum_bernoulli (n : ℕ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n :=
begin
  induction n with n ih, { simp },
  rw [finset.sum_range_succ],
  rw [nat.choose_succ_self_right],
  rw [bernoulli_def, mul_sub, mul_one, sub_add_eq_add_sub, sub_eq_iff_eq_add],
  rw [add_left_cancel_iff, finset.mul_sum, finset.sum_congr rfl],
  intros k hk, rw finset.mem_range at hk,
  rw [mul_div_right_comm, ← mul_assoc],
  congr' 1,
  rw [← mul_div_assoc, eq_div_iff],
  { rw [mul_comm ((n+1 : ℕ) : ℚ)],
    have hk' : k ≤ n + 1, by linarith,
    rw_mod_cast nat.choose_mul_succ_eq n k },
  { contrapose! hk with H, rw sub_eq_zero at H, norm_cast at H, linarith }
end
