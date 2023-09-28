/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import analysis.special_functions.log.deriv

/-!
# Estimates on natural log of rationals close to 1
-/

open filter finset set
open_locale topology big_operators

namespace real

lemma artanh_partial_series_bound_aux {y : ℝ} (n : ℕ) (hy₁ : -1 < y) (hy₂ : y < 1) :
  deriv (λ (x : ℝ), (∑ i in range n, x^(2*i+1)/(2*i+1)) - 1/2 * log ((1+x)/(1-x))) y =
    - (y^2)^n / (1 - y^2) :=
begin
  have : (∑ i in range n, (2*↑i+1) * y ^ (2*i) / (2*i+1)) = (∑ i in range n, (y^2) ^ i),
  { congr' with i,
    have : 2 * (i : ℝ) + 1 ≠ 0 := by exact_mod_cast (nat.succ_ne_zero (2 * i)),
    field_simp [this, mul_comm, ←pow_mul] },
  have hy' : 0 < 1 + y, simpa [add_comm] using sub_pos_of_lt hy₁,
  have hy'' : y^2 ≠ 1 := by simp [hy₁.ne', hy₂.ne],
  field_simp [this, hy'.ne', hy'.ne, hy₂.ne, hy₂.ne', hy'', geom_sum_eq,
    sub_ne_zero_of_ne, hy''.symm],
  ring
end

lemma artanh_partial_series_upper_bound {x : ℝ} (h : |x| < 1) (n : ℕ) :
  |((∑ i in range n, x^(2*i+1)/(2*i+1)) - 1/2 * log ((1+x)/(1-x)))| ≤ (|x|)^(2*n+1) / (1 - x^2) :=
begin
  let F : ℝ → ℝ := λ x, (∑ i in range n, x^(2*i+1)/(2*i+1)) - 1/2 * log ((1+x)/(1-x)),
  have B : ∀ y ∈ Icc (-|x|) (|x|), |deriv F y| ≤ |x|^(2*n) / (1 - x^2),
  { intros y hy,
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨(neg_lt_neg h).trans_le hy.1, hy.2.trans_lt h⟩,
    rw [artanh_partial_series_bound_aux _ this.1 this.2, abs_div, abs_neg, ←pow_abs, ←pow_abs,
      pow_mul, abs_of_pos (show 0 < 1 - y^2, by simpa [abs_lt] using this)],
    simp only [pow_bit0_abs],
    have := abs_le.2 hy,
    have yx : y^2 ≤ x^2 := sq_le_sq.2 (abs_le.2 hy),
    exact div_le_div (pow_nonneg (sq_nonneg _) _) (pow_le_pow_of_le_left (sq_nonneg _) yx _)
      (by simpa using h) (sub_le_sub_left yx _) },
  have C : ‖F x - F 0‖ ≤ (|x|^(2*n) / (1 - x^2)) * ‖x - 0‖,
  { have : ∀ y ∈ Icc (- |x|) (|x|), differentiable_at ℝ F y,
    { intros y hy,
      have hy' : 0 < 1 + y := neg_lt_iff_pos_add'.1 ((neg_lt_neg h).trans_le hy.1),
      simp [F, sub_ne_zero_of_ne (hy.2.trans_lt h).ne', hy'.ne'] },
    apply convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _,
    { simp },
    { simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)] } },
  simpa [F, norm_eq_abs, pow_succ', div_mul_eq_mul_div, mul_assoc] using C,
end

lemma newbound {x : ℝ} (h : |x| < 1) (n : ℕ) :
  |(2*(∑ i in range n, x^(2*i+1)/(2*i+1)) - log ((1+x)/(1-x)))| ≤ 2 * (|x|)^(2*n+1) / (1 - x^2) :=
begin
  /- For the proof, we show that the derivative of the function to be estimated is small,
  and then apply the mean value inequality. -/
  let F : ℝ → ℝ := λ x, 2*(∑ i in range n, x^(2*i+1)/(2*i+1)) - log ((1+x)/(1-x)),
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv F y = - 2 * ((y^2)^n) / (1 - y^2),
  { intros y hy,
    have : (∑ i in range n, (2*↑i+1) * y ^ (2*i) / (2*i+1)) = (∑ i in range n, (y^2) ^ i),
    { congr' with i,
      have : 2 * (i : ℝ) + 1 ≠ 0 := by exact_mod_cast (nat.succ_ne_zero (2 * i)),
      field_simp [this, mul_comm, ←pow_mul] },
    have hy' : 0 < 1 + y, simpa [add_comm] using sub_pos_of_lt hy.1,
    have hy'' : y^2 ≠ 1 := by simp [hy.1.ne', hy.2.ne],
    field_simp [F, this, hy'.ne', hy'.ne, hy.2.ne, hy.2.ne', hy'', geom_sum_eq,
      sub_ne_zero_of_ne, hy''.symm],
    ring },
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-|x|) (|x|), |deriv F y| ≤ 2 * |x|^(2*n) / (1 - x^2),
  { intros y hy,
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨(neg_lt_neg h).trans_le hy.1, hy.2.trans_lt h⟩,
    rw [A y this, abs_div, abs_mul, ←pow_abs, ←pow_abs, pow_mul, abs_neg, abs_two, pow_bit0_abs,
      pow_bit0_abs, abs_of_pos (show 0 < 1 - y^2, by simpa [abs_lt] using this)],
    simp only [abs_div, ←pow_abs, abs_mul, pow_mul, pow_bit0_abs y, abs_neg, abs_two],
    have : 0 < 1 - x^2, by simpa using h,
    have yx : y^2 ≤ x^2,
    { rw sq_le_sq,
      rwa abs_le },
    refine div_le_div (mul_nonneg zero_le_two (pow_nonneg (sq_nonneg _) _)) _ this
      (sub_le_sub_left yx _),
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (sq_nonneg _) yx _) zero_le_two },
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ ≤ (2 * |x|^(2*n) / (1 - x^2)) * ‖x - 0‖,
  { have : ∀ y ∈ Icc (- |x|) (|x|), differentiable_at ℝ F y,
    { intros y hy,
      have hy' : 0 < 1 + y := neg_lt_iff_pos_add'.1 ((neg_lt_neg h).trans_le hy.1),
      simp [F, sub_ne_zero_of_ne (hy.2.trans_lt h).ne', hy'.ne'] },
    apply convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _,
    { simp },
    { simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)] } },
  simpa [F, norm_eq_abs, pow_succ', div_mul_eq_mul_div, mul_assoc] using C,
end

-- lemma log_two_near_10 : |log 2 - 836158 / 1206321| ≤ 1/10^10 :=
-- begin
--   suffices : |log 2 - 836158 / 1206321| ≤ 1/17179869184 + (1/10^10 - 1/2^34),
--   { norm_num1 at *,
--     assumption },
--   have t : |(2⁻¹ : ℝ)| = 2⁻¹,
--   { rw abs_of_pos, norm_num },
--   have z := real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : ℝ)| < 1, by { rw t, norm_num }) 34,
--   rw t at z,
--   norm_num1 at z,
--   rw [one_div (2:ℝ), log_inv, ←sub_eq_add_neg, _root_.abs_sub_comm] at z,
--   apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _),
--   simp_rw [sum_range_succ],
--   norm_num,
--   rw abs_of_pos;
--   norm_num
-- end

lemma log_two_near_20 : |log 2 - 48427462327/69866059742| < 9/10^21 :=
begin
  have t : |(3⁻¹ : ℝ)| = 3⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(3⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 21,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((9 : ℝ)/10^21),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_neg, abs_of_pos],
  by { norm_num1 },
  by { norm_num1 },
end

lemma log_two_gt_d20 : 0.69314718055994530940 < log 2 :=
(sub_lt_comm.1 (abs_sub_lt_iff.1 log_two_near_20).2).trans_le' (by norm_num1)

lemma log_two_lt_d20 : log 2 < 0.69314718055994530943 :=
lt_of_lt_of_le (sub_lt_iff_lt_add.1 (abs_sub_lt_iff.1 log_two_near_20).1) (by norm_num)

lemma log_three_div_two_near_20 : |log (3/2) - 31251726476/77076241213| < 1/10^22 :=
begin
  have t : |(5⁻¹ : ℝ)| = 5⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(5⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 17,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((1 : ℝ)/10^22),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_neg, abs_of_pos],
  { norm_num1 },
  { norm_num1 },
end.

lemma log_four_div_three_near_20 : |log (4/3) - 4349275835861/15118341573370| < 1/10^26 :=
begin
  have t : |(7⁻¹ : ℝ)| = 7⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(7⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 16,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((1 : ℝ)/10^26),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_of_pos],
  { norm_num1 },
  { norm_num1 },
end.

lemma log_nine_div_eight_near_20 : |log (9/8) - 26418276175004 / 224296105358295| < 3/10^29 :=
begin
  have t : |(17⁻¹ : ℝ)| = 17⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(17⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 12,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((3 : ℝ)/10^29),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_neg, abs_of_pos],
  { norm_num1 },
  { norm_num1 },
end.


lemma log_two_near_20'' : |log 2 - 1148067618206 / 1656311459391| < 5/10^25 :=
begin
  have : (log 2 - (2*4349275835861/15118341573370 + 26418276175004 / 224296105358295)) =
    2*(log ((2*2)/3) - 4349275835861/15118341573370) +
      (log ((3*3)/(2*2*2)) - 26418276175004 / 224296105358295),
  { rw [mul_sub, ←sub_sub, add_sub_assoc', sub_left_inj, mul_div_assoc, sub_add_eq_add_sub,
      sub_left_inj, log_div, log_div, log_mul, log_mul, log_mul, log_mul],
    { ring },
    all_goals { norm_num } },
  rw [←sub_add_sub_cancel, this],
  apply (abs_add_three _ _ _).trans_lt _,
  rw [abs_mul, abs_two, (show (3 : ℝ) * 3 = 9, by norm_num1), (show (2 : ℝ) * 2 = 4, by norm_num1),
    (show (4 : ℝ) * 2 = 8, by norm_num1)],
  have e₁ := mul_lt_mul_of_pos_left log_four_div_three_near_20 zero_lt_two,
  apply (add_lt_add_right (add_lt_add e₁ log_nine_div_eight_near_20) _).trans_le _,
  rw [abs_of_nonneg],
  { norm_num1 },
  { norm_num1 },
end

lemma log_three_near_20 :
  |log 3 - 12397791320721 / 11284955983654| < 4/10^26 :=
begin
  have : (log 3 - (2 * (26418276175004/224296105358295) + 3 * (4349275835861/15118341573370))) =
    2 * (log (3^2/2^3) - 26418276175004/224296105358295) +
      3 * (log(2^2/3) - 4349275835861/15118341573370),
  { rw [log_div, log_div, log_pow, log_pow, log_pow, nat.cast_two, nat.cast_bit1, nat.cast_one],
    { ring_nf },
    all_goals {norm_num} },
  rw [←sub_add_sub_cancel, this],
  apply (abs_add_three _ _ _).trans_lt _,
  rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2, by norm_num1),
    abs_of_pos (show (0 : ℝ) < 3, by norm_num1), (show (3 : ℝ) ^ 2 = 9, by norm_num1),
    (show (2 : ℝ) ^ 3 = 8, by norm_num1), (show (2 : ℝ) ^ 2 = 4, by norm_num1)],
  have e₁ := mul_lt_mul_of_pos_left log_four_div_three_near_20 (show (0 : ℝ) < 3, by norm_num1),
  have e₂ := mul_lt_mul_of_pos_left log_nine_div_eight_near_20 (show (0 : ℝ) < 2, by norm_num1),
  apply (add_lt_add_right (add_lt_add e₂ e₁) _).trans_le _,
  rw abs_of_nonpos,
  { norm_num1 },
  { norm_num1 },
end

-- the proof does better than this
lemma log_three_gt_d20 : 1.0986122886681096 < log 3 :=
(sub_lt_comm.1 (abs_sub_lt_iff.1 log_three_near_20).2).trans_le' (by norm_num1)

-- the proof does better than this
lemma log_three_lt_d20 : log 3 < 1.0986122886681097 :=
lt_of_lt_of_le (sub_lt_iff_lt_add.1 (abs_sub_lt_iff.1 log_three_near_20).1) (by norm_num)

lemma log_64_div_63_near : |log (64/63) - 87664200650948 / 5566561694550313| < 4/10^32 :=
begin
  have t : |(127⁻¹ : ℝ)| = 127⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(127⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 8,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((4 : ℝ)/10^32),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  rw [abs_of_nonneg];
  norm_num1,
end.

lemma abs_add_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| :=
(abs_add _ _).trans (add_le_add_right (abs_add_three _ _ _) _)

lemma log_seven_near : |log 7 - 5543595633008 / 2848844606571| < 6/10^24 :=
begin
  have : (log 7 - _) =
    (-1) * (log ((2^6) / (3^2*7)) - 87664200650948 / 5566561694550313) +
      (-2) * (log 3 - 12397791320721 / 11284955983654) +
        6 * (log 2 -  1148067618206 / 1656311459391),
  { rw [log_div, log_pow, log_mul, log_pow, nat.cast_bit0, nat.cast_bit1, nat.cast_one,
      nat.cast_two],
    { ring_nf },
    all_goals {norm_num} },
  rw [←sub_add_sub_cancel, this],
  apply (abs_add_four _ _ _ _).trans_lt _,
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_one, abs_neg, abs_two, one_mul,
    abs_of_pos (show (0 : ℝ) < 6, by norm_num1), (show (2^6:ℝ) / (3^2*7) = 64/63, by norm_num1)],
  have e₁ := log_64_div_63_near,
  have e₂ := mul_lt_mul_of_pos_left log_three_near_20 two_pos,
  have e₃ := mul_lt_mul_of_pos_left log_two_near_20'' (show (0 : ℝ) < 6, by norm_num1),
  refine (add_lt_add_right (add_lt_add (add_lt_add e₁ e₂) e₃) _).trans_le _,
  rw abs_of_nonpos,
  { norm_num1 },
  { norm_num1 },
end

lemma log_25_div_24_near : |log (25/24) - 7010006310925/171721308410023| < 4/10^30 :=
begin
  have t : |(49⁻¹ : ℝ)| = 49⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(49⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 9,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((4 : ℝ)/10 ^ 30),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_of_pos],
  { norm_num1 },
  { norm_num1 },
end

lemma log_five_near : |log 5 - 25218653206049 / 15669230239462| < 2/10^24 :=
begin
  have : (log 5 - _) =
    (1/2) * (log ((5^2) / (2^3*3)) - 7010006310925/171721308410023) +
      (1/2) * (log 3 - 12397791320721 / 11284955983654) +
        (3/2) * (log 2 - 1148067618206 / 1656311459391),
  { rw [log_div, log_pow, log_mul, log_pow, nat.cast_bit1, nat.cast_one, nat.cast_two],
    { ring_nf },
    all_goals {norm_num} },
  rw [←sub_add_sub_cancel, this],
  apply (abs_add_four _ _ _ _).trans_lt _,
  rw [abs_mul, abs_mul, abs_mul, abs_div, abs_div, abs_two, abs_one,
    abs_of_pos (show (0 : ℝ) < 3, by norm_num1),
    (show (5^2:ℝ) / (2^3*3) = 25/24, by norm_num1)],
  have e₁ := mul_lt_mul_of_pos_left log_25_div_24_near (show (0 : ℝ) < 1 / 2, by norm_num1),
  have e₂ := mul_lt_mul_of_pos_left log_three_near_20 (show (0 : ℝ) < 1 / 2, by norm_num1),
  have e₃ := mul_lt_mul_of_pos_left log_two_near_20'' (show (0 : ℝ) < 3 / 2, by norm_num1),
  refine (add_lt_add_right (add_lt_add (add_lt_add e₁ e₂) e₃) _).trans_le _,
  rw abs_of_nonpos,
  { norm_num1 },
  { norm_num1 },
end

-- the proof does better than this
lemma log_five_gt_d20 : 1.609437912434100374 < log 5 :=
(sub_lt_comm.1 (abs_sub_lt_iff.1 log_five_near).2).trans_le' (by norm_num1)

-- the proof does better than this
lemma log_five_lt_d20 : log 5 < 1.609437912434100375 :=
lt_of_lt_of_le (sub_lt_iff_lt_add.1 (abs_sub_lt_iff.1 log_five_near).1) (by norm_num)

lemma log_8_div_7_near : |log (8/7) - 94488369352/707611652173| < 9/10^26 :=
begin
  have t : |(15⁻¹ : ℝ)| = 15⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(15⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 11,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((9 : ℝ)/10^26),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_of_pos],
  { norm_num1 },
  { norm_num1 },
end.


lemma log_16_div_15_near : |log (16/15) - 2777280486178 / 43032911774627| < 7/10^28 :=
begin
  have t : |(31⁻¹ : ℝ)| = 31⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(31⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 10,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((7 : ℝ)/10^28),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_of_neg],
  { norm_num1 },
  { norm_num1 },
end.

lemma log_33_div_32_near : |log (33/32) - 63667272858575 / 2069023108181113| < 3/10^31 :=
begin
  have t : |(65⁻¹ : ℝ)| = 65⁻¹ := abs_of_pos (by norm_num1),
  have z := newbound (show |(65⁻¹ : ℝ)| < 1, by { rw t, norm_num1 }) 9,
  rw [t, _root_.abs_sub_comm] at z,
  norm_num1 at z,
  rw ←add_sub_cancel'_right _ ((3 : ℝ)/10^31),
  apply (_root_.abs_sub_le _ _ _).trans_lt (add_lt_add_of_le_of_lt z _),
  simp_rw [sum_range_succ, sum_range_zero],
  norm_num1,
  rw [abs_of_neg],
  { norm_num1 },
  { norm_num1 },
end.

end real
