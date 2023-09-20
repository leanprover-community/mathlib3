/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import analysis.special_functions.log.deriv
import analysis.special_functions.log.base

noncomputable theory

open real

-- def logb (x : ℝ) : ℝ := log x / log 2

-- lemma logb_lt_logb {x y : ℝ} (hx : 0 < x) (h : x < y) : logb x < logb y :=
-- div_lt_div_of_lt (log_pos one_lt_two) (log_lt_log hx h)

-- lemma log_le_log' {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : log x ≤ log y :=
-- (log_le_log hx (hx.trans_le h)).2 h

-- lemma logb_le_logb {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : logb x ≤ logb y :=
-- div_le_div_of_le (log_nonneg one_le_two) (log_le_log' hx h)

lemma logb_pow {b x : ℝ} (m : ℕ) : logb b (x ^ m) = m * logb b x :=
by rw [logb, log_pow, mul_div_assoc, logb]

lemma logb_zpow {b x : ℝ} (m : ℤ) : logb b (x ^ m) = m * logb b x :=
by rw [logb, log_zpow, mul_div_assoc, logb]

lemma log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hy : x ≤ y) : log x ≤ log y :=
(log_le_log hx (hx.trans_le hy)).2 hy

lemma logb_le_logb_of_le {b x y : ℝ} (hb : 1 ≤ b) (hx : 0 < x) (hy : x ≤ y) : logb b x ≤ logb b y :=
div_le_div_of_le (log_nonneg hb) (log_le_log_of_le hx hy)

lemma logb_base {b : ℝ} (hb : 0 < b) (hb' : b ≠ 1) : logb b b = 1 :=
div_self (log_ne_zero_of_pos_of_ne_one hb hb')

lemma logb_div_base' {b x : ℝ} (hb : 0 < b) (hb' : b ≠ 1) (hx : x ≠ 0) :
  logb b (x / b) = logb b x - 1 :=
by rw [logb_div hx hb.ne', logb_base hb hb']

-- (log_le_log hx (hx.trans_le hy)).2 hy

-- lemma logb_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : logb (x * y) = logb x + logb y :=
-- by rw [logb, logb, logb, log_mul hx hy, add_div]

-- lemma logb_two : logb 2 = 1 :=
-- by { rw [logb, div_self (log_ne_zero_of_pos_of_ne_one _ _)]; norm_num }

-- lemma logb_two_mul {x : ℝ} (hx : x ≠ 0) : logb (2 * x) = 1 + logb x :=
-- by rw [logb_mul two_ne_zero hx, logb_two]

-- lemma logb_div_two {x : ℝ} (hx : x ≠ 0) :
--   logb (x / 2) = logb x - 1 :=
-- by rw [eq_sub_iff_add_eq', ←logb_two_mul (div_ne_zero hx two_ne_zero),
--   mul_div_cancel' x two_ne_zero]

def log_base2_goal (x₁ x₂ a₁ a₂ : ℝ) : Prop :=
0 < x₁ → x₁ ≤ x₂ → a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂

lemma log_base2_square {x₁ x₂ a₁ a₂ : ℝ} (h : log_base2_goal (x₁ ^ 2) (x₂ ^ 2) (2 * a₁) (2 * a₂)) :
  log_base2_goal x₁ x₂ a₁ a₂ :=
λ hx₁ hx₂, by simpa [logb_pow] using h (pow_pos hx₁ _) (pow_le_pow_of_le_left hx₁.le hx₂ _)

lemma log_base2_weaken {x₁ x₂ a₁ a₂ : ℝ} (x₃ x₄ : ℝ) (h : log_base2_goal x₃ x₄ a₁ a₂)
  (h₁ : x₃ ≤ x₁) (h₂ : x₂ ≤ x₄) (h₃ : 0 < x₃) :
  log_base2_goal x₁ x₂ a₁ a₂ :=
begin
  intros hx₁ hx₂,
  have t := h h₃ (h₁.trans (hx₂.trans h₂)),
  exact ⟨t.1.trans_le (logb_le_logb_of_le one_le_two h₃ h₁),
         t.2.trans_le' (logb_le_logb_of_le one_le_two (hx₁.trans_le hx₂) h₂)⟩,
end

lemma log_base2_half {x₁ x₂ a₁ a₂ : ℝ}
  (h : log_base2_goal (x₁ / 2) (x₂ / 2) (a₁ - 1) (a₂ - 1)) :
  log_base2_goal x₁ x₂ a₁ a₂ :=
λ hx₁ hx₂,
by simpa [logb_div_base', hx₁.ne', (show (2 : ℝ) ≠ 1, by norm_num), (hx₁.trans_le hx₂).ne'] using
    h (half_pos hx₁) (div_le_div_of_le zero_le_two hx₂)

lemma log_base2_scale {x₁ x₂ a₁ a₂ : ℝ} (m : ℤ)
  (h : log_base2_goal (x₁ * 2^m) (x₂ * 2^m) (a₁ + m) (a₂ + m)) :
  log_base2_goal x₁ x₂ a₁ a₂ :=
begin
  intros hx₁ hx₂,
  have i : 0 < (2 : ℝ)^m := zpow_pos_of_pos zero_lt_two _,
  have := h (mul_pos hx₁ i) (mul_le_mul_of_nonneg_right hx₂ i.le),
  simpa [logb_mul hx₁.ne' i.ne', logb_mul (hx₁.trans_le hx₂).ne' i.ne', logb_zpow, logb_base,
    (show (2 : ℝ) ≠ 1, by norm_num)] using this,
end

lemma log_base2_start {x₁ x₂ a₁ a₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : x₁ ≤ x₂)
  (h : log_base2_goal x₁ x₂ a₁ a₂) : a₁ < logb 2 x₁ ∧ logb 2 x₂ < a₂ :=
h hx₁ hx₂

lemma log_base2_end {x₁ x₂ a₁ a₂ : ℝ} (hx₁ : 1 < x₁) (hx₂ : x₂ < 2) (ha₁ : a₁ ≤ 0) (ha₂ : 1 ≤ a₂) :
  log_base2_goal x₁ x₂ a₁ a₂ :=
begin
  rintro - h,
  refine ⟨ha₁.trans_lt (div_pos (log_pos hx₁) (log_pos one_lt_two)), lt_of_lt_of_le _ ha₂⟩,
  rw [logb, div_lt_one (log_pos one_lt_two)],
  exact log_lt_log ((zero_le_one.trans_lt hx₁).trans_le h) hx₂,
end

namespace tactic
namespace interactive

setup_tactic_parser

meta def weaken (t u : parse parser.pexpr) : tactic unit :=
`[refine log_base2_weaken %%t %%u _ (by norm_num1) (by norm_num1) (by norm_num1)]
-- tactic.refine ``(log_base2_weaken %%t %%u _ (by norm_num1) (by norm_num1) _)
-- tactic.refine (log_base2_weaken _ _ _ _ _ _)

end interactive
end tactic

-- -- proved implicitly in log_small.lean
-- lemma log2_lower_bound : 0.6931471805599453094171 < log 2 := sorry
-- lemma log2_upper_bound : log 2 < 0.6931471805599453094174 := sorry

-- -- set_option profiler true

-- lemma logb_log2 : (-0.5287664) < logb 2 (log 2) ∧ logb 2 (log 2) < (-0.5287663) :=
-- begin
--   refine log_base2_start (log_pos one_lt_two) le_rfl _,
--   refine log_base2_weaken _ _ _ log2_lower_bound.le log2_upper_bound.le (by norm_num1),
--   apply log_base2_scale 1,
--   rw int.cast_one,
--   refine log_base2_square _,
--   refine log_base2_weaken 1.921812055672805698667 1.921812055672805698670 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.84668078866466761509 1.84668078866466761511 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.70511496761157938741 1.70511496761157938746 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.4537085263865187116 1.4537085263865187118 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.0566342398444318845 1.0566342398444318849 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.1164759168116204050 1.1164759168116204059 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.246518472820348326 1.246518472820348329 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.55380830308237346 1.55380830308237348 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.20716012136386247 1.20716012136386251 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   -- refine log_base2_weaken 1.4572355586112151 1.4572355586112153 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_weaken 1.45723554 1.4572400 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   weaken 1.0617677 1.0617956,
--   refine log_base2_square _,
--   weaken 1.12735 1.12741,
--   refine log_base2_square _,
--   weaken 1.270914 1.271054,
--   refine log_base2_square _,
--   weaken 1.61522 1.61558,
--   refine log_base2_square _,
--   refine log_base2_half _,
--   weaken 1.30446 1.30506,
--   refine log_base2_square _,
--   weaken 1.7016 1.7032,
--   refine log_base2_square _,
--   refine log_base2_half _,
--   weaken 1.4477 1.4505,
--   refine log_base2_square _,
--   refine log_base2_half _,
--   weaken 1.0479 1.0526,
--   refine log_base2_square _,
--   weaken 1.098 1.108,
--   refine log_base2_square _,
--   weaken 1.196 1.228,
--   refine log_base2_square _,
--   weaken 1.43 1.53,
--   refine log_base2_square _,
--   refine log_base2_half _,
--   weaken 1.01 1.18,
--   refine log_base2_square _,
--   weaken 1.01 1.41,
--   refine log_base2_square _,
--   norm_num1,
--   exact log_base2_end (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1),
-- end

-- lemma logb_log2' : (-0.5287664) < logb (log 2) ∧ logb (log 2) < (-0.5287663) :=
-- begin
--   refine log_base2_start (log_pos one_lt_two) le_rfl _,
--   refine log_base2_weaken _ _ _ log2_lower_bound.le log2_upper_bound.le (by norm_num1),
--   apply log_base2_scale 1,
--   rw int.cast_one,
--   refine log_base2_square _,
--   refine log_base2_weaken 1.921812055672805698667 1.921812055672805698670 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.84668078866466761509 1.84668078866466761511 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.70511496761157938741 1.70511496761157938746 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.4537085263865187116 1.4537085263865187118 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.0566342398444318845 1.0566342398444318849 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.1164759168116204050 1.1164759168116204059 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.246518472820348326 1.246518472820348329 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.55380830308237346 1.55380830308237348 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.20716012136386247 1.20716012136386251 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.4572355586112151 1.4572355586112153 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.0617677366404700 1.0617677366404704 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.127350726570626 1.127350726570628 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.27091966069931 1.27091966069933 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.6152367839520 1.6152367839522 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.304494934115 1.304494934117 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.701707033131 1.701707033137 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.44790341330 1.44790341332 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.04821214712 1.04821214716 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.0987487053 1.0987487055 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.2072487173 1.2072487179 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.457449465 1.457449467 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_half _,
--   refine log_base2_weaken 1.062079471 1.062079475 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   refine log_base2_weaken 1.12801280 1.12801282 _ (by norm_num1) (by norm_num1) (by norm_num1),
--   refine log_base2_square _,
--   norm_num1,
--   exact log_base2_end (by norm_num1) (by norm_num1) (by norm_num1) (by norm_num1),
-- end

-- example : (-0.3665130) < log (log 2) ∧ log (log 2) < (-0.3665128) :=
-- begin
--   have i : 0 < log 2 := log_pos one_lt_two,
--   have t := logb_log2,
--   rw [logb, lt_div_iff i, div_lt_iff i] at t,
--   refine ⟨lt_of_le_of_lt _ t.1, lt_of_lt_of_le t.2 _⟩,
--   { exact le_trans (by norm_num) (mul_le_mul_of_nonpos_left log2_upper_bound.le (by norm_num1)) },
--   { exact (mul_le_mul_of_nonpos_left log2_lower_bound.le (by norm_num1)).trans (by norm_num) },
-- end
