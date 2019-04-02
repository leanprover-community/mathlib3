/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import analysis.exponential

namespace real
variable (x : ℝ)

/-- the series `sqrt_two_add_series x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2`
-/
@[simp] noncomputable def sqrt_two_add_series (x : ℝ) : ℕ → ℝ
| 0     := x
| (n+1) := sqrt (2 + sqrt_two_add_series n)

lemma sqrt_two_add_series_zero : sqrt_two_add_series x 0 = x := by simp
lemma sqrt_two_add_series_one : sqrt_two_add_series 0 1 = sqrt 2 := by simp
lemma sqrt_two_add_series_two : sqrt_two_add_series 0 2 = sqrt (2 + sqrt 2) := by simp

lemma sqrt_two_add_series_zero_nonneg : ∀(n : ℕ), sqrt_two_add_series 0 n ≥ 0
| 0     := le_refl 0
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_nonneg {x : ℝ} (h : 0 ≤ x) : ∀(n : ℕ), sqrt_two_add_series x n ≥ 0
| 0     := h
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_lt_two : ∀(n : ℕ), sqrt_two_add_series 0 n < 2
| 0     := by norm_num
| (n+1) :=
  begin
    refine lt_of_lt_of_le _ (le_of_eq $ sqrt_sqr $ le_of_lt two_pos),
    rw [sqrt_two_add_series, sqrt_lt],
    apply add_lt_of_lt_sub_left,
    apply lt_of_lt_of_le (sqrt_two_add_series_lt_two n),
    norm_num, apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg, norm_num
  end

lemma sqrt_two_add_series_succ (x : ℝ) :
  ∀(n : ℕ), sqrt_two_add_series x (n+1) = sqrt_two_add_series (sqrt (2 + x)) n
| 0     := rfl
| (n+1) := by rw [sqrt_two_add_series, sqrt_two_add_series_succ, sqrt_two_add_series]

lemma sqrt_two_add_series_monotone_left {x y : ℝ} (h : x ≤ y) :
  ∀(n : ℕ), sqrt_two_add_series x n ≤ sqrt_two_add_series y n
| 0     := h
| (n+1) :=
  begin
    rw [sqrt_two_add_series, sqrt_two_add_series],
    apply sqrt_le_sqrt, apply add_le_add_left, apply sqrt_two_add_series_monotone_left
  end

lemma sqrt_two_add_series_step_up {a b n : ℕ} {z : ℝ} (c d : ℕ)
  (hz : sqrt_two_add_series (c/d) n ≤ z) (hb : b ≠ 0) (hd : d ≠ 0)
  (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) : sqrt_two_add_series (a/b) (n+1) ≤ z :=
begin
  refine le_trans _ hz, rw [sqrt_two_add_series_succ], apply sqrt_two_add_series_monotone_left,
  rwa [sqrt_le_left, div_pow, add_div_eq_mul_add_div, div_le_iff, mul_comm (_/_), ←mul_div_assoc,
      le_div_iff, ←nat.cast_pow, ←nat.cast_pow, ←@nat.cast_one ℝ, ←nat.cast_bit0, ←nat.cast_mul,
      ←nat.cast_mul, ←nat.cast_add, ←nat.cast_mul, nat.cast_le, mul_comm b],
  apply pow_pos, iterate 2 {apply nat.cast_pos.2, apply nat.pos_of_ne_zero, assumption},
  exact nat.cast_ne_zero.2 hb,
  exact nat.cast_ne_zero.2 hd,
  exact div_nonneg (nat.cast_nonneg _) (nat.cast_pos.2 $ nat.pos_of_ne_zero hd)
end

lemma sqrt_two_add_series_step_down {c d n : ℕ} {z : ℝ} (a b : ℕ)
  (hz : z ≤ sqrt_two_add_series (a/b) n) (hb : b ≠ 0) (hd : d ≠ 0)
  (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) : z ≤ sqrt_two_add_series (c/d) (n+1) :=
begin
  apply le_trans hz, rw [sqrt_two_add_series_succ], apply sqrt_two_add_series_monotone_left,
  apply le_sqrt_of_sqr_le,
  rwa [div_pow, add_div_eq_mul_add_div, div_le_iff, mul_comm (_/_), ←mul_div_assoc,
      le_div_iff, ←nat.cast_pow, ←nat.cast_pow, ←@nat.cast_one ℝ, ←nat.cast_bit0, ←nat.cast_mul,
      ←nat.cast_mul, ←nat.cast_add, ←nat.cast_mul, nat.cast_le, mul_comm (b ^ 2)],
  swap, apply pow_pos, iterate 2 {apply nat.cast_pos.2, apply nat.pos_of_ne_zero, assumption},
  exact nat.cast_ne_zero.2 hd,
  exact nat.cast_ne_zero.2 hb
end

@[simp] lemma cos_pi_over_two_pow : ∀(n : ℕ), cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2
| 0     := by simp
| (n+1) :=
  begin
    symmetry, rw [div_eq_iff_mul_eq], symmetry,
    rw [sqrt_two_add_series, sqrt_eq_iff_sqr_eq, mul_pow, cos_square, ←mul_div_assoc,
      nat.add_succ, pow_succ, mul_div_mul_left, cos_pi_over_two_pow, add_mul],
    congr, norm_num,
    rw [mul_comm, pow_two, mul_assoc, ←mul_div_assoc, mul_div_cancel_left, ←mul_div_assoc,
        mul_div_cancel_left],
    norm_num, norm_num, apply pow_ne_zero, norm_num, norm_num,
    apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg, norm_num,
    apply le_of_lt, apply mul_pos, apply cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two,
    { transitivity (0 : ℝ), rw neg_lt_zero, apply pi_div_two_pos,
      apply div_pos pi_pos, apply pow_pos, norm_num },
    apply div_lt_div' (le_refl pi) _ pi_pos _,
    refine lt_of_le_of_lt (le_of_eq (pow_one _).symm) _,
    apply pow_lt_pow, norm_num, apply nat.succ_lt_succ, apply nat.succ_pos, all_goals {norm_num}
  end

lemma sin_square_pi_over_two_pow (n : ℕ) :
  sin (pi / 2 ^ (n+1)) ^ 2 = 1 - (sqrt_two_add_series 0 n / 2) ^ 2 :=
by rw [sin_square, cos_pi_over_two_pow]

lemma sin_square_pi_over_two_pow_succ (n : ℕ) :
  sin (pi / 2 ^ (n+2)) ^ 2 = 1 / 2 - sqrt_two_add_series 0 n / 4 :=
begin
  rw [sin_square_pi_over_two_pow, sqrt_two_add_series, div_pow, sqr_sqrt, add_div, ←sub_sub],
  congr, norm_num, norm_num, apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg,
  norm_num
end

@[simp] lemma sin_pi_over_two_pow_succ (n : ℕ) :
  sin (pi / 2 ^ (n+2)) = sqrt (2 - sqrt_two_add_series 0 n) / 2 :=
begin
  symmetry, rw [div_eq_iff_mul_eq], symmetry,
  rw [sqrt_eq_iff_sqr_eq, mul_pow, sin_square_pi_over_two_pow_succ, sub_mul],
  { congr, norm_num, rw [mul_comm], convert mul_div_cancel' _ _, norm_num, norm_num },
  { rw [sub_nonneg], apply le_of_lt, apply sqrt_two_add_series_lt_two },
  apply le_of_lt, apply mul_pos, apply sin_pos_of_pos_of_lt_pi,
  { apply div_pos pi_pos, apply pow_pos, norm_num },
  refine lt_of_lt_of_le _ (le_of_eq (div_one _)), rw [div_lt_div_left],
  refine lt_of_le_of_lt (le_of_eq (pow_zero 2).symm) _,
  apply pow_lt_pow, norm_num, apply nat.succ_pos, apply pi_pos,
  apply pow_pos, all_goals {norm_num}
end

lemma cos_pi_div_four : cos (pi / 4) = sqrt 2 / 2 :=
by { transitivity cos (pi / 2 ^ 2), congr, norm_num, simp }

lemma sin_pi_div_four : sin (pi / 4) = sqrt 2 / 2 :=
by { transitivity sin (pi / 2 ^ 2), congr, norm_num, simp }

lemma cos_pi_div_eight : cos (pi / 8) = sqrt (2 + sqrt 2) / 2 :=
by { transitivity cos (pi / 2 ^ 3), congr, norm_num, simp }

lemma sin_pi_div_eight : sin (pi / 8) = sqrt (2 - sqrt 2) / 2 :=
by { transitivity sin (pi / 2 ^ 3), congr, norm_num, simp }

lemma cos_pi_div_sixteen : cos (pi / 16) = sqrt (2 + sqrt (2 + sqrt 2)) / 2 :=
by { transitivity cos (pi / 2 ^ 4), congr, norm_num, simp }

lemma sin_pi_div_sixteen : sin (pi / 16) = sqrt (2 - sqrt (2 + sqrt 2)) / 2 :=
by { transitivity sin (pi / 2 ^ 4), congr, norm_num, simp }

lemma cos_pi_div_thirty_two : cos (pi / 32) = sqrt (2 + sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity cos (pi / 2 ^ 5), congr, norm_num, simp }

lemma sin_pi_div_thirty_two : sin (pi / 32) = sqrt (2 - sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity sin (pi / 2 ^ 5), congr, norm_num, simp }

lemma pi_gt_sqrt_two_add_series (n : ℕ) : pi > 2 ^ (n+1) * sqrt (2 - sqrt_two_add_series 0 n) :=
begin
  have : pi > sqrt (2 - sqrt_two_add_series 0 n) / 2 * 2 ^ (n+2),
  { apply mul_lt_of_lt_div, apply pow_pos, norm_num,
    rw [←sin_pi_over_two_pow_succ], apply sin_lt, apply div_pos pi_pos, apply pow_pos, norm_num },
  apply lt_of_le_of_lt (le_of_eq _) this,
  rw [pow_succ _ (n+1), ←mul_assoc, div_mul_cancel, mul_comm], norm_num
end

lemma pi_lt_sqrt_two_add_series (n : ℕ) :
  pi < 2 ^ (n+1) * sqrt (2 - sqrt_two_add_series 0 n) + 1 / 4 ^ n :=
begin
  have : pi < (sqrt (2 - sqrt_two_add_series 0 n) / 2 + 1 / (2 ^ n) ^ 3 / 4) * 2 ^ (n+2),
  { rw [←div_lt_iff, ←sin_pi_over_two_pow_succ],
    refine lt_of_lt_of_le (lt_add_of_sub_right_lt (sin_gt_sub_cube _ _)) _,
    { apply div_pos pi_pos, apply pow_pos, norm_num },
    { apply div_le_of_le_mul, apply pow_pos, norm_num, refine le_trans pi_le_four _,
      simp only [show ((4 : ℝ) = 2 ^ 2), by norm_num, mul_one],
      apply pow_le_pow, norm_num, apply le_add_of_nonneg_left, apply nat.zero_le },
    apply add_le_add_left, rw div_le_div_right,
    apply le_div_of_mul_le, apply pow_pos, apply pow_pos, norm_num,
    rw [←mul_pow],
    refine le_trans _ (le_of_eq (one_pow 3)), apply pow_le_pow_of_le_left,
    { apply le_of_lt, apply mul_pos, apply div_pos pi_pos, apply pow_pos, norm_num, apply pow_pos,
      norm_num },
    apply mul_le_of_le_div, apply pow_pos, norm_num,
    refine le_trans ((div_le_div_right _).mpr pi_le_four) _, apply pow_pos, norm_num,
    rw [pow_succ, pow_succ, ←mul_assoc, ←field.div_div_eq_div_mul],
    convert le_refl _, norm_num, norm_num, apply pow_ne_zero, norm_num, norm_num,
    apply pow_pos, norm_num },
  apply lt_of_lt_of_le this (le_of_eq _), rw [add_mul], congr' 1,
  { rw [pow_succ _ (n+1), ←mul_assoc, div_mul_cancel, mul_comm], norm_num },
  rw [pow_succ, ←pow_mul, mul_comm n 2, pow_mul, show (2 : ℝ) ^ 2 = 4, by norm_num, pow_succ,
      pow_succ, ←mul_assoc (2 : ℝ), show (2 : ℝ) * 2 = 4, by norm_num, ←mul_assoc, div_mul_cancel,
      mul_comm ((2 : ℝ) ^ n), ←div_div_eq_div_mul, div_mul_cancel],
  apply pow_ne_zero, norm_num, norm_num
end

lemma pi_gt_three : pi > 3 :=
begin
  refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series 1), rw [mul_comm],
  apply le_mul_of_div_le, norm_num, apply le_sqrt_of_sqr_le, rw [le_sub],
  rw show (0:ℝ) = (0:ℕ)/(1:ℕ), by rw [nat.cast_zero, zero_div],
  apply sqrt_two_add_series_step_up 23 16,
  all_goals {norm_num}
end

lemma pi_gt_314 : pi > 3.14 :=
begin
  refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series 4), rw [mul_comm],
  apply le_mul_of_div_le, norm_num, apply le_sqrt_of_sqr_le,
  rw [le_sub, show (0:ℝ) = (0:ℕ)/(1:ℕ), by rw [nat.cast_zero, zero_div]],
  apply sqrt_two_add_series_step_up 99 70,
  apply sqrt_two_add_series_step_up 874 473,
  apply sqrt_two_add_series_step_up 1940 989,
  apply sqrt_two_add_series_step_up 1447 727,
  all_goals {norm_num}
end

lemma pi_lt_315 : pi < 3.15 :=
begin
  refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series 4) _,
  apply add_le_of_le_sub_right, rw [mul_comm], apply mul_le_of_le_div, apply pow_pos, norm_num,
  rw [sqrt_le_left, sub_le, show (0:ℝ) = (0:ℕ)/(1:ℕ), by rw [nat.cast_zero, zero_div]],
  apply sqrt_two_add_series_step_down 140 99,
  apply sqrt_two_add_series_step_down 279 151,
  apply sqrt_two_add_series_step_down 51 26,
  apply sqrt_two_add_series_step_down 412 207,
  all_goals {norm_num}
end

/- A computation of the first 7 digits of pi is given here:
  https://gist.github.com/fpvandoorn/5b405988bc2e61953d56e3597db16ecf
  This is not included in mathlib, because of slow compilation time.
  -/

end real
