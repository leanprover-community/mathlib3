/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, 1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ is even then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

Note however that this result is not yet formalised in Lean.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

Note that $B_1=+1/2$, meaning that we are using the $B_n^+$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).
To get the "minus" convention, just use `(-1)^n * bernoulli n`.

There is no particular reason that the `+` convention was used.
In some sense it's like choosing whether you want to sum over `fin n`
(so `j < n`) or sum over `j ≤ n` (or `nat.antidiagonal n`). Indeed
$$(t+1)\sum_{j\lt n}j^t=\sum_{k\leq t}\binom{t+1}{k}B_k^{-}n^{t+1-k}$$
and
$$(t+1)\sum_{j\leq n}j^t=\sum_{k\leq t}\binom{t+1}{k}B_k^{+}n^{t+1-k}.$$

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$.

## Main theorems

`sum_bernoulli : ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n`

## Todo

* `∑ k : fin n, n.binomial k * (-1)^k * bernoulli k = if n = 1 then 1 else 0`

* Bernoulli polynomials

* `∑ k : fin n, k ^ t =` the Bernoulli polynomial B_t evaluated at n

* `∑ k : fin n.succ, n.succ.choose k bernoulli_poly k X = n.succ * X ^ n` as polynomials
-/

open_locale big_operators

/-!

### Definitions

-/

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - ∑ k : fin n, n.choose k / (n - k + 1) * bernoulli k k.2)

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, (n.choose k) / (n - k + 1) * bernoulli k :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, (n.choose k) / (n - k + 1) * bernoulli k :=
by { rw [bernoulli_def', ← fin.sum_univ_eq_sum_range], refl }

/-!

### Examples

-/

section examples

open finset

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl

@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 :=
begin
    rw [bernoulli_def, sum_range_one], norm_num
end

@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one],
  rw (show nat.choose 4 2 = 6, from dec_trivial), -- shrug
  norm_num,
end

end examples

open nat finset

@[simp] lemma sum_bernoulli (n : ℕ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n :=
begin
  cases n with n, { simp },
  rw [sum_range_succ, bernoulli_def],
  suffices : (n + 1 : ℚ) * ∑ k in range n, (n.choose k : ℚ) / (n - k + 1) * bernoulli k =
    ∑ x in range n, (n.succ.choose x : ℚ) * bernoulli x,
  { rw [← this, choose_succ_self_right], norm_cast, ring},
  simp_rw [mul_sum, ← mul_assoc],
  apply sum_congr rfl,
  intros k hk, replace hk := le_of_lt (mem_range.1 hk),
  rw ← cast_sub hk,
  congr',
  field_simp [show ((n - k : ℕ) : ℚ) + 1 ≠ 0, by {norm_cast, simp}],
  -- down to nat
  norm_cast,
  rw [mul_comm, nat.sub_add_eq_add_sub hk],
  exact choose_mul_succ_eq n k,
end
