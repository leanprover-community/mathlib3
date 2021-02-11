/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import data.real.irrational

/-!
# Liouville's theorem
This file will contain a proof of Liouville's theorem stating that all Liouville numbers are
transcendental.

At the moment, it contains the definition of a Liouville number and a proof that Liouville
numbers are irrational.

The commented imports below will appear as they are needed.  I (Damiano) leave them here for
ease of reference.
--import data.polynomial.denoms_clearable
--import ring_theory.algebraic
--import topology.algebra.polynomial
--import analysis.calculus.mean_value
-/

section irrational

/--
A Liouville number is a real number `x` such that for every natural number `n`, there exist
`a, b ∈ ℤ` with `1 < b` such that `0 < |x - a/b| < 1/bⁿ`.
In the implementation, the condition `x ≠ a/b` replaces the traditional equivalent `0 < |x - a/b|`.
-/
def is_liouville (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ,
  1 < b ∧ x ≠ a / b ∧ abs (x - a / b) < 1 / b ^ n

namespace is_liouville

lemma irrational {x : ℝ} (h : is_liouville x) : irrational x :=
begin
  rintros ⟨⟨a, b, bN0, cop⟩, rfl⟩,
  change (is_liouville (a / b)) at h,
  rcases h (b + 1) with ⟨p, q, q1, a0, a1⟩,
  have qR0 : (0 : ℝ) < q := int.cast_pos.mpr (zero_lt_one.trans q1),
  have b0 : (b : ℝ) ≠ 0 := ne_of_gt (nat.cast_pos.mpr bN0),
  have bq0 : (0 : ℝ) < b * q := mul_pos (nat.cast_pos.mpr bN0) qR0,
  replace a1 : abs (a * q - b * p) * q ^ (b + 1) < b * q, by
    rwa [div_sub_div _ _ b0 (ne_of_gt qR0), abs_div, div_lt_div_iff (abs_pos.mpr (ne_of_gt bq0))
      (pow_pos qR0 _), abs_of_pos bq0, one_mul, ← int.cast_pow, ← int.cast_mul, ← int.cast_coe_nat,
      ← int.cast_mul, ← int.cast_mul, ← int.cast_sub, ← int.cast_abs, ← int.cast_mul, int.cast_lt]
        at a1,
  replace a0 : ¬a * q - ↑b * p = 0, by
    rwa [ne.def, div_eq_div_iff b0 (ne_of_gt qR0), mul_comm ↑p, ← sub_eq_zero_iff_eq,
      ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_mul, ← int.cast_sub, int.cast_eq_zero] at a0,
  lift q to ℕ using (zero_lt_one.trans q1).le,
  have ap : 0 < abs (a * ↑q - ↑b * p) := abs_pos.mpr a0,
  lift (abs (a * ↑q - ↑b * p)) to ℕ using (abs_nonneg (a * ↑q - ↑b * p)),
  rw [← int.coe_nat_mul, ← int.coe_nat_pow, ← int.coe_nat_mul, int.coe_nat_lt] at a1,
  exact not_le.mpr a1 (nat.mul_lt_mul_pow_succ (int.coe_nat_pos.mp ap) (int.coe_nat_lt.mp q1)).le,
end

end is_liouville

end irrational
