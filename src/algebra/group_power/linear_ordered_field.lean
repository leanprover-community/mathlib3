/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.group_power.lemmas
import data.nat.cast
/-!
# Lemmas about power operations on fields

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `zsmul`
which require additional imports besides those available in `algebra.group_power.lemmas`.
-/

/-- Bernoulli's inequality reformulated to estimate `(n : K)`. -/
theorem nat.cast_le_pow_sub_div_sub {K : Type*} [linear_ordered_field K] {a : K} (H : 1 < a)
  (n : ℕ) :
  (n : K) ≤ (a ^ n - 1) / (a - 1) :=
(le_div_iff (sub_pos.2 H)).2 $ le_sub_left_of_add_le $
  one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem nat.cast_le_pow_div_sub {K : Type*} [linear_ordered_field K] {a : K} (H : 1 < a) (n : ℕ) :
  (n : K) ≤ a ^ n / (a - 1) :=
(n.cast_le_pow_sub_div_sub H).trans $ div_le_div_of_le (sub_nonneg.2 H.le)
  (sub_le_self _ zero_le_one)
