/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import number_theory.liouville.basic
/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `transcendental_liouville_number`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$.  However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number.  Classically, the Liouville number for $m = 2$ is the one called
``Liouville's constant''.

## Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$.  However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/

noncomputable theory
open_locale nat big_operators
open real finset

/--
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouville_number (m : ℝ) : ℝ := ∑' (i : ℕ), 1 / m ^ i!

namespace liouville_number

/--
`liouville_number.partial_sum` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def partial_sum (m : ℝ) (k : ℕ) : ℝ := ∑ i in range (k+1), 1 / m ^ i!

/--
`liouville_number.remainder` is the sum of the series of the terms in `liouville_number m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def remainder (m : ℝ) (k : ℕ) : ℝ := ∑' i, 1 / m ^ (i + (k+1))!

/-!
We start with simple observations.
-/

protected lemma summable {m : ℝ} (hm : 1 < m) : summable (λ i : ℕ, 1 / m ^ i!) :=
summable_one_div_pow_of_le hm nat.self_le_factorial

lemma remainder_summable {m : ℝ} (hm : 1 < m) (k : ℕ) :
  summable (λ i : ℕ, 1 / m ^ (i + (k + 1))!) :=
by convert (summable_nat_add_iff (k + 1)).2 (liouville_number.summable hm)

lemma remainder_pos {m : ℝ} (hm : 1 < m) (k : ℕ) : 0 < remainder m k :=
tsum_pos (remainder_summable hm k) (λ _, by positivity) 0 (by positivity)

lemma partial_sum_succ (m : ℝ) (n : ℕ) :
  partial_sum m (n + 1) = partial_sum m n + 1 / m ^ (n + 1)! :=
sum_range_succ _ _

/--  Split the sum definining a Liouville number into the first `k` term and the rest. -/
lemma partial_sum_add_remainder {m : ℝ} (hm : 1 < m) (k : ℕ) :
  partial_sum m k + remainder m k = liouville_number m  :=
sum_add_tsum_nat_add _ (liouville_number.summable hm)

/-! We now prove two useful inequalities, before collecting everything together. -/

/--  An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying `1 < m` and is
stronger than the estimate `liouville_number.remainder_lt` below. However, the latter estimate is
more useful for the proof. -/
lemma remainder_lt' (n : ℕ) {m : ℝ} (m1 : 1 < m) :
  remainder m n < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
-- two useful inequalities
have m0 : 0 < m := zero_lt_one.trans m1,
have mi : 1 / m < 1 := (div_lt_one m0).mpr m1,
calc (∑' i, 1 / m ^ (i + (n + 1))!)
    < ∑' i, 1 / m ^ (i + (n + 1)!) :
    -- to show the strict inequality between these series, we prove that:
    tsum_lt_tsum
      -- 1. the second series dominates the first
      (λ b, one_div_pow_le_one_div_pow_of_le m1.le (b.add_factorial_succ_le_factorial_add_succ n))
      -- 2. the term with index `i = 2` of the first series is strictly smaller than
      -- the corresponding term of the second series
      (one_div_pow_strict_anti m1 (n.add_factorial_succ_lt_factorial_add_succ le_rfl))
      -- 3. the first series is summable
      (remainder_summable m1 n)
      -- 4. the second series is summable, since its terms grow quickly
      (summable_one_div_pow_of_le m1 (λ j, le_self_add))
... = ∑' i : ℕ, (1 / m) ^ i * (1 / m ^ (n + 1)!) :
    -- split the sum in the exponent and massage
    by simp only [pow_add, one_div, mul_inv, inv_pow]
-- factor the constant `(1 / m ^ (n + 1)!)` out of the series
... = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) : tsum_mul_right
... = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :
    -- the series if the geometric series
    by rw [tsum_geometric_of_lt_1 (by positivity) mi]

lemma aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) :
  (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n!) ^ n :=
calc (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :
  -- the second factors coincide (and are non-negative),
  -- the first factors, satisfy the inequality `sub_one_div_inv_le_two`
  mul_le_mul_of_nonneg_right (sub_one_div_inv_le_two hm) (by positivity)
... = 2 / m ^ (n + 1)! : mul_one_div 2 _
... = 2 / m ^ (n! * (n + 1)) : congr_arg ((/) 2) (congr_arg (pow m) (mul_comm _ _))
... ≤ 1 / m ^ (n! * n) :
  begin
    -- [ NB: in this block, I do not follow the brace convention for subgoals -- I wait until
    --   I solve all extraneous goals at once with `exact pow_pos (zero_lt_two.trans_le hm) _`. ]
    -- Clear denominators and massage*
    apply (div_le_div_iff _ _).mpr,
    conv_rhs { rw [one_mul, mul_add, pow_add, mul_one, pow_mul, mul_comm, ← pow_mul] },
    -- the second factors coincide, so we prove the inequality of the first factors*
    refine (mul_le_mul_right _).mpr _,
    -- solve all the inequalities `0 < m ^ ??`
    any_goals { exact pow_pos (zero_lt_two.trans_le hm) _ },
    -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
    exact trans (trans hm (pow_one _).symm.le) (pow_mono (one_le_two.trans hm) n.factorial_pos)
  end
... = 1 / (m ^ n!) ^ n : congr_arg ((/) 1) (pow_mul m n! n)

/--  An upper estimate on the remainder. This estimate works with `m ∈ ℝ` satisfying `2 ≤ m` and is
weaker than the estimate `liouville_number.remainder_lt'` above. However, this estimate is
more useful for the proof. -/
lemma remainder_lt (n : ℕ) {m : ℝ} (m2 : 2 ≤  m) :
  remainder m n < 1 / (m ^ n!) ^ n :=
(remainder_lt' n $ one_lt_two.trans_le m2).trans_le (aux_calc _ m2)

/-!  Starting from here, we specialize to the case in which `m` is a natural number. -/

/--  The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
lemma partial_sum_eq_rat {m : ℕ} (hm : 0 < m) (k : ℕ) :
  ∃ p : ℕ, partial_sum m k = p / m ^ k! :=
begin
  induction k with k h,
  { exact ⟨1, by rw [partial_sum, range_one, sum_singleton, nat.cast_one]⟩ },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    rw [partial_sum_succ, h_k, div_add_div, div_eq_div_iff, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ, add_mul, one_mul, add_tsub_cancel_right, pow_add],
      simp [mul_assoc] },
    all_goals { positivity } }
end

end liouville_number

open liouville_number

theorem liouville_liouville_number {m : ℕ} (hm : 2 ≤ m) :
  liouville (liouville_number m) :=
begin
  -- two useful inequalities
  have mZ1 : 1 < (m : ℤ), { norm_cast, exact one_lt_two.trans_le hm },
  have m1 : 1 < (m : ℝ), { norm_cast, exact one_lt_two.trans_le hm },
  intro n,
  -- the first `n` terms sum to `p / m ^ k!`
  rcases partial_sum_eq_rat (zero_lt_two.trans_le hm) n with ⟨p, hp⟩,
  refine ⟨p, m ^ n!, one_lt_pow mZ1 n.factorial_ne_zero, _⟩,
  push_cast,
  -- separate out the sum of the first `n` terms and the rest
  rw [← partial_sum_add_remainder m1 n, ← hp],
  have hpos := remainder_pos m1 n,
  simpa [abs_of_pos hpos, hpos.ne'] using @remainder_lt n m (by assumption_mod_cast)
end

lemma transcendental_liouville_number {m : ℕ} (hm : 2 ≤ m) :
  transcendental ℤ (liouville_number m) :=
(liouville_liouville_number hm).transcendental
