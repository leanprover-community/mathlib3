/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import algebra.char_p.invertible
import analysis.specific_limits
/-!

# Lemmas on inequalities and series for Liouville constants

This file contains lemmas about inequalities and series that are used in the proof to show that
transcendental Liouville numbers exist.
-/

open_locale nat big_operators
open set real

variable {m : ℝ}

lemma one_div_pow_strict_mono_decr_on : strict_mono_decr_on (λ x : ℝ, 1 / x) (set.Ioi 0) :=
λ x x1 y y1 xy, (one_div_lt_one_div (mem_Ioi.mp y1) (mem_Ioi.mp x1)).mpr xy

lemma one_div_mono_exp (m1 : 1 ≤ m) {a b : ℕ} (ab : a ≤ b) :
  1 / m ^ b ≤ 1 / m ^ a :=
begin
  refine (one_div_le_one_div _ _).mpr (pow_le_pow m1 ab);
  exact pow_pos (lt_of_lt_of_le zero_lt_one m1) _
end

lemma one_div_pow_strict_mono (m1 : 1 < m) {a b : ℕ} (ab : a < b) :
  1 / m ^ b < 1 / m ^ a :=
begin
  refine one_div_pow_strict_mono_decr_on _ _ (pow_lt_pow m1 ab);
  exact pow_pos (zero_lt_one.trans m1) _
end

section lemmas_about_summability_and_sums

/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
lemma summable_one_div_pow_of_le {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
  summable (λ i, 1 / m ^ f i) :=
begin
  refine summable_of_nonneg_of_le
    (λ a, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (λ a, _)
    (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
      ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm))),
  rw [div_pow, one_pow],
  refine (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (fi a));
  exact pow_pos (zero_lt_one.trans hm) _
end

end lemmas_about_summability_and_sums

/--  Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/
lemma tsum_one_div_pow_factorial_lt (m1 : 1 < m) (n : ℕ) :
  ∑' (i : ℕ), 1 / m ^ (i + (n + 1))! < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
-- two useful inequalities
have m0 : 0 < m := (zero_lt_one.trans m1),
have mi : abs (1 / m) < 1 :=
  (le_of_eq (abs_of_pos (one_div_pos.mpr m0))).trans_lt ((div_lt_one m0).mpr m1),
calc (∑' i, 1 / m ^ (i + (n + 1))!)
    < ∑' i, 1 / m ^ (i + (n + 1)!) :
    -- to show the strict inequality between these series, we prove that:
    tsum_lt_tsum_of_nonneg
      -- 1. the first series has non-negative terms
      (λ b, one_div_nonneg.mpr (pow_nonneg m0.le _))
      -- 2. the second series dominates the first
      (λ b, one_div_mono_exp m1.le (b.add_factorial_succ_le_factorial_add_succ n))
      -- 3. the term with index `i = 2` of the first series is strictly smaller than
      -- the corresponding term of the second series
      (one_div_pow_strict_mono m1 (n.add_factorial_succ_lt_factorial_add_succ rfl.le))
      -- 4. the second series is summable, since its terms grow quickly
      (summable_one_div_pow_of_le m1 (λ j, nat.le.intro rfl))
... = ∑' i, (1 / m) ^ i * (1 / m ^ (n + 1)!) :
    -- split the sum in the exponent and massage
    by { congr, ext i, rw [pow_add, ← div_div_eq_div_mul, div_eq_mul_one_div, ← one_div_pow i] }
-- factor the constant `(1 / m ^ (n + 1)!)` out of the series
... = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) : tsum_mul_right
... = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :
    -- the series if the geometric series
    mul_eq_mul_right_iff.mpr (or.inl (tsum_geometric_of_abs_lt_1 mi))

lemma liouville.aux_calc (n : ℕ) (hm : 2 ≤ m) :
  (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n!) ^ n :=
calc (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :
  -- the second factors coincide (and are non-negative),
  -- the first factors, satisfy the inequality `sub_one_div_inv_le_two`
  mul_mono_nonneg (one_div_nonneg.mpr (pow_nonneg (zero_le_two.trans hm) _))
    (sub_one_div_inv_le_two hm)
... = 2 / m ^ (n + 1)! : mul_one_div 2 _
... = 2 / m ^ (n! * (n + 1)) : congr_arg ((/) 2) (congr_arg (pow m) (mul_comm _ _))
... ≤ 1 / m ^ (n! * n) :
  begin
    -- [ NB: in this block, I did not follow the brace convention for subgoals.  The
    --   reason is that all extraneous goals are solved by
    --   `exact pow_pos (zero_lt_two.trans_le hm) _` and are created also by later tactics.
    --   Thus, I waited until the last tactic producing a repeated goal and then solve them
    --   all at once using `any_goals { exact pow_pos (zero_lt_two.trans_le hm) _ }`. ]
    -- Clear denominators and massage*
    apply (div_le_div_iff _ _).mpr,
    conv_rhs { rw [one_mul, mul_add, pow_add, mul_one, pow_mul, mul_comm, ← pow_mul] },
    -- the second factors coincide, so we prove the inequality of the first factors*
    apply (mul_le_mul_right _).mpr,
    -- solve all the inequalities `0 < m ^ ??`
    any_goals { exact pow_pos (zero_lt_two.trans_le hm) _ },
    -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
    exact trans (trans hm (pow_one _).symm.le) (pow_mono (one_le_two.trans hm) n.factorial_pos)
  end
... = 1 / (m ^ n!) ^ n : congr_arg ((/) 1) (pow_mul m n! n)
