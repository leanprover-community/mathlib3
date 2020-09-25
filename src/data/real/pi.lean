/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Benjamin Davidson
-/
import analysis.special_functions.pow

namespace real

lemma pi_gt_sqrt_two_add_series (n : ℕ) : 2 ^ (n+1) * sqrt (2 - sqrt_two_add_series 0 n) < pi :=
begin
  have : sqrt (2 - sqrt_two_add_series 0 n) / 2 * 2 ^ (n+2) < pi,
  { rw [← lt_div_iff, ←sin_pi_over_two_pow_succ], apply sin_lt, apply div_pos pi_pos,
    all_goals { apply pow_pos, norm_num } },
  apply lt_of_le_of_lt (le_of_eq _) this,
  rw [pow_succ _ (n+1), ←mul_assoc, div_mul_cancel, mul_comm], norm_num
end

lemma pi_lt_sqrt_two_add_series (n : ℕ) :
  pi < 2 ^ (n+1) * sqrt (2 - sqrt_two_add_series 0 n) + 1 / 4 ^ n :=
begin
  have : pi < (sqrt (2 - sqrt_two_add_series 0 n) / 2 + 1 / (2 ^ n) ^ 3 / 4) * 2 ^ (n+2),
  { rw [← div_lt_iff, ← sin_pi_over_two_pow_succ],
    refine lt_of_lt_of_le (lt_add_of_sub_right_lt (sin_gt_sub_cube _ _)) _,
    { apply div_pos pi_pos, apply pow_pos, norm_num },
    { rw div_le_iff',
      { refine le_trans pi_le_four _,
        simp only [show ((4 : ℝ) = 2 ^ 2), by norm_num, mul_one],
        apply pow_le_pow, norm_num, apply le_add_of_nonneg_left, apply nat.zero_le },
        { apply pow_pos, norm_num }},
    apply add_le_add_left, rw div_le_div_right,
    rw [le_div_iff, ←mul_pow],
    refine le_trans _ (le_of_eq (one_pow 3)), apply pow_le_pow_of_le_left,
    { apply le_of_lt, apply mul_pos, apply div_pos pi_pos, apply pow_pos, norm_num, apply pow_pos,
      norm_num },
    rw ← le_div_iff,
    refine le_trans ((div_le_div_right _).mpr pi_le_four) _, apply pow_pos, norm_num,
    rw [pow_succ, pow_succ, ←mul_assoc, ←div_div_eq_div_mul],
    convert le_refl _,
    all_goals { repeat {apply pow_pos}, norm_num }},
  apply lt_of_lt_of_le this (le_of_eq _), rw [add_mul], congr' 1,
  { rw [pow_succ _ (n+1), ←mul_assoc, div_mul_cancel, mul_comm], norm_num },
  rw [pow_succ, ←pow_mul, mul_comm n 2, pow_mul, show (2 : ℝ) ^ 2 = 4, by norm_num, pow_succ,
      pow_succ, ←mul_assoc (2 : ℝ), show (2 : ℝ) * 2 = 4, by norm_num, ←mul_assoc, div_mul_cancel,
      mul_comm ((2 : ℝ) ^ n), ←div_div_eq_div_mul, div_mul_cancel],
  apply pow_ne_zero, norm_num, norm_num
end

/-- From an upper bound on `sqrt_two_add_series 0 n = 2 cos (pi / 2 ^ (n+1))` of the form
`sqrt_two_add_series 0 n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2)`, one can deduce the lower bound `a < pi`
thanks to basic trigonometric inequalities as expressed in `pi_gt_sqrt_two_add_series`. -/
theorem pi_lower_bound_start (n : ℕ) {a}
  (h : sqrt_two_add_series ((0:ℕ) / (1:ℕ)) n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2) : a < pi :=
begin
  refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series n), rw [mul_comm],
  refine (div_le_iff (pow_pos (by norm_num) _ : (0 : ℝ) < _)).mp (le_sqrt_of_sqr_le _),
  rwa [le_sub, show (0:ℝ) = (0:ℕ)/(1:ℕ), by rw [nat.cast_zero, zero_div]],
end

lemma sqrt_two_add_series_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ}
  (hz : sqrt_two_add_series (c/d) n ≤ z) (hb : 0 < b) (hd : 0 < d)
  (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) : sqrt_two_add_series (a/b) (n+1) ≤ z :=
begin
  refine le_trans _ hz, rw sqrt_two_add_series_succ, apply sqrt_two_add_series_monotone_left,
  have hb' : 0 < (b:ℝ) := nat.cast_pos.2 hb,
  have hd' : 0 < (d:ℝ) := nat.cast_pos.2 hd,
  rw [sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg), div_pow,
    add_div_eq_mul_add_div _ _ (ne_of_gt hb'), div_le_div_iff hb' (pow_pos hd' _)],
  exact_mod_cast h
end

/-- Create a proof of `a < pi` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ a/2^(n+1)`. -/
meta def pi_lower_bound (l : list ℚ) : tactic unit :=
do let n := l.length,
  tactic.apply `(@pi_lower_bound_start %%(reflect n)),
  l.mmap' (λ r, do
    let a := r.num.to_nat, let b := r.denom,
    (() <$ tactic.apply `(@sqrt_two_add_series_step_up %%(reflect a) %%(reflect b)));
    [tactic.skip, `[norm_num1], `[norm_num1], `[norm_num1]]),
  `[simp only [sqrt_two_add_series, nat.cast_bit0, nat.cast_bit1, nat.cast_one, nat.cast_zero]],
  `[norm_num1]

/-- From a lower bound on `sqrt_two_add_series 0 n = 2 cos (pi / 2 ^ (n+1))` of the form
`2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrt_two_add_series 0 n`, one can deduce the upper bound
`pi < a` thanks to basic trigonometric formulas as expressed in `pi_lt_sqrt_two_add_series`. -/
theorem pi_upper_bound_start (n : ℕ) {a}
  (h : 2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrt_two_add_series ((0:ℕ) / (1:ℕ)) n)
  (h₂ : 1 / 4 ^ n ≤ a) : pi < a :=
begin
  refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series n) _,
  rw [← le_sub_iff_add_le, ← le_div_iff', sqrt_le_left, sub_le],
  { rwa [nat.cast_zero, zero_div] at h },
  { exact div_nonneg (sub_nonneg.2 h₂) (pow_nonneg (le_of_lt two_pos) _) },
  { exact pow_pos two_pos _ }
end

lemma sqrt_two_add_series_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
  (hz : z ≤ sqrt_two_add_series (a/b) n) (hb : 0 < b) (hd : 0 < d)
  (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) : z ≤ sqrt_two_add_series (c/d) (n+1) :=
begin
  apply le_trans hz, rw sqrt_two_add_series_succ, apply sqrt_two_add_series_monotone_left,
  apply le_sqrt_of_sqr_le,
  have hb' : 0 < (b:ℝ) := nat.cast_pos.2 hb,
  have hd' : 0 < (d:ℝ) := nat.cast_pos.2 hd,
  rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'), div_le_div_iff (pow_pos hb' _) hd'],
  exact_mod_cast h
end

/-- Create a proof of `pi < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ (a - 1/4^n) / 2^(n+1)`. -/
meta def pi_upper_bound (l : list ℚ) : tactic unit :=
do let n := l.length,
  (() <$ tactic.apply `(@pi_upper_bound_start %%(reflect n))); [pure (), `[norm_num1]],
  l.mmap' (λ r, do
    let a := r.num.to_nat, let b := r.denom,
    (() <$ tactic.apply `(@sqrt_two_add_series_step_down %%(reflect a) %%(reflect b)));
    [pure (), `[norm_num1], `[norm_num1], `[norm_num1]]),
  `[simp only [sqrt_two_add_series, nat.cast_bit0, nat.cast_bit1, nat.cast_one, nat.cast_zero]],
  `[norm_num]

lemma pi_gt_three : 3 < pi := by pi_lower_bound [23/16]

lemma pi_gt_314 : 3.14 < pi := by pi_lower_bound [99/70, 874/473, 1940/989, 1447/727]

lemma pi_lt_315 : pi < 3.15 := by pi_upper_bound [140/99, 279/151, 51/26, 412/207]

lemma pi_gt_31415 : 3.1415 < pi := by pi_lower_bound [
  11482/8119, 5401/2923, 2348/1197, 11367/5711, 25705/12868, 23235/11621]

lemma pi_lt_31416 : pi < 3.1416 := by pi_upper_bound [
  4756/3363, 101211/54775, 505534/257719, 83289/41846,
  411278/205887, 438142/219137, 451504/225769, 265603/132804, 849938/424971]

lemma pi_gt_3141592 : 3.141592 < pi := by pi_lower_bound [
  11482/8119, 7792/4217, 54055/27557, 949247/476920, 3310126/1657059,
  2635492/1318143, 1580265/790192, 1221775/610899, 3612247/1806132, 849943/424972]

lemma pi_lt_3141593 : pi < 3.141593 := by pi_upper_bound [
  27720/19601, 56935/30813, 49359/25163, 258754/130003, 113599/56868, 1101994/551163,
  8671537/4336095, 3877807/1938940, 52483813/26242030, 56946167/28473117, 23798415/11899211]


noncomputable theory
open real filter
open_locale classical big_operators topological_space
local notation `|`x`|` := abs x
local notation `π` := real.pi

-- The following theorem will be removed:
theorem mvt (f f':ℝ→ℝ) {a b c:ℝ} (h : a ≤ b) (hderiv : ∀ (x ∈ set.Icc a b), has_deriv_at f (f' x) x)
  (hbound : ∀ (x ∈ set.Icc a b), |f' x| ≤ c) : |f b - f a| ≤ c * (b - a) :=
begin
  rw ← norm_eq_abs (f b - f a),
  apply norm_image_sub_le_of_norm_deriv_le_segment',
  { intros x hx,
    exact (hderiv x hx).has_deriv_within_at },
  { intros x hx,
    rw norm_eq_abs (f' x),
    exact hbound x (set.Ico_subset_Icc_self hx) },
  { exact set.right_mem_Icc.mpr h },
end


/-! ### Leibniz's Series for Pi
`∑ (-1)^i / (2*i+1)` from `i=1` to `n` tends to `π/4` as `n` tends to `+∞` -/

lemma leibniz : tendsto (λ k, ∑ i in finset.range k, ((-(1:ℝ))^i / (2*i+1))) at_top (𝓝 (π/4)) :=
begin
  let b := λ (i:ℕ) x, (-(1:ℝ))^i * x^(2*i+1) / (2*i+1),
  let g := λ x (k:ℕ), ∑ i in finset.range k, b i x,
  let f := λ (k:ℕ) x, arctan x - g x k,
  let w := λ (k:ℕ), ((1 - (((k:nnreal) ^ (-1 / (2*(k:ℝ)+1))):nnreal)):ℝ) + 1/k,
  have H : ∀ k, ∥∑ i in finset.range k, ((-(1:ℝ))^i / (2*i+1)) - π/4∥ ≤ w k,
  { have f_bound : ∀ k, |f k 1| ≤ w k,
    { intro k,
      have f0 : f k 0 = 0 := by { simp only [f, g, b], simp },
      let f' := λ (y:ℝ), (-y^2) ^ k / (1 + y^2),
      have has_deriv_at_f : ∀ (x:ℝ), has_deriv_at (f k) (f' x) x,
      { intro x,
        have b_deriv : ∀ (i:ℕ), i ∈ finset.range k → (has_deriv_at (b i) ((-x^2)^i) x),
        { intros i hi,
          convert has_deriv_at.const_mul ((-1:ℝ)^i / (2*i+1)) (@has_deriv_at.pow _ _ _ _ _ (2*i+1)
                    (has_deriv_at_id x)),
          { ext y, simp only [b, id.def], ring },
          { simp only [nat.add_succ_sub_one, add_zero, mul_one, id.def, nat.cast_bit0, nat.cast_add,
                        nat.cast_one, nat.cast_mul],
            rw [← mul_assoc, @div_mul_cancel _ _ _ (2*(i:ℝ)+1) (by {norm_cast, linarith}),
                pow_mul x 2 i, ← mul_pow (-1) (x^2) i],
            ring } },
        convert has_deriv_at.sub (has_deriv_at_arctan x) (has_deriv_at.sum b_deriv),
        have g_sum := @geom_sum _ _ (-x^2) (by linarith [neg_nonpos.mpr (pow_two_nonneg x)]) k,
        simp only [geom_series, f'] at g_sum ⊢,
        rw [g_sum, ← neg_add' (x^2) 1, add_comm (x^2) 1, sub_eq_add_neg, neg_div', neg_div_neg_eq],
        ring },
      let a_k := (k:nnreal) ^ (-1 / (2 * (k:ℝ) + 1)),
      have h1 : (a_k:ℝ) ≤ 1,
      { simp [a_k],
        by_cases hk1 : k = 0,
        { rw hk1,
          exact zero_rpow_le_one (-1 / (2 * 0 + 1)) },
        { have hk2 : 1 ≤ (k:ℝ) := by { norm_cast, exact nat.succ_le_iff.mpr (nat.pos_of_ne_zero hk1) },
          exact rpow_le_one_of_one_le_of_nonpos hk2 (le_of_lt (@div_neg_of_neg_of_pos _ _
                  (-(1:ℝ)) (2*(k:ℝ)+1) (by norm_num) (by {norm_cast, linarith} ))) } },
      have h2 : 0 ≤ (a_k:ℝ) := zero_le (a_k),
      have f'_bound : ∀ (y ∈ set.Icc (-1:ℝ) 1), |f' y| ≤ |y|^(2*k),
      { intros y hy,
        rw [abs_div, is_monoid_hom.map_pow abs (-y^2) k, abs_neg, is_monoid_hom.map_pow abs y 2,
            tactic.ring_exp.pow_e_pf_exp rfl rfl, @abs_of_pos _ _ (1+y^2) (by nlinarith)],
        convert @div_le_div_of_le_left _ _ _ (1+y^2) 1 (pow_nonneg (abs_nonneg y) (2*k))
                    (by norm_num) (by nlinarith),
        simp },
      have f_deriv1 : ∀ (x:ℝ), x ∈ set.Icc (a_k:ℝ) 1 → has_deriv_at (f k) (f' x) x,
      { intros y hy,
        exact has_deriv_at_f y },
      have f_deriv2 : ∀ (x:ℝ), x ∈ set.Icc 0 (a_k:ℝ) → has_deriv_at (f k) (f' x) x,
      { intros y hy,
        exact has_deriv_at_f y },
      have hbound1 : ∀ (y ∈ set.Icc (a_k:ℝ) 1), |f' y| ≤ 1,
      { intros y hy,
        cases hy,
        have hincr := pow_le_pow_of_le_left (le_trans h2 hy_left) hy_right (2*k),
        rw [one_pow (2*k), ← abs_of_nonneg (le_trans h2 hy_left)] at hincr,
        rw ← abs_of_nonneg (le_trans h2 hy_left) at hy_right,
        linarith [f'_bound y (set.mem_Icc.mpr (abs_le.mp hy_right))] },
      have hbound2 : ∀ (y ∈ set.Icc 0 (a_k:ℝ)), |f' y| ≤ a_k ^ (2*k),
      { intros y hy,
        cases hy,
        have hincr := pow_le_pow_of_le_left hy_left hy_right (2*k),
        rw ← abs_of_nonneg hy_left at hincr hy_right,
        rw ← abs_of_nonneg h2 at h1 hy_right,
        linarith [f'_bound y (set.mem_Icc.mpr (abs_le.mp (le_trans hy_right h1)))] },
      have mvt1 := mvt (f k) f' h1 f_deriv1 hbound1,
      ring at mvt1,
      have mvt2 := mvt (f k) f' h2 f_deriv2 hbound2,
      simp only [f0, nnreal.coe_zero, sub_zero] at mvt2,
      rw ← pow_succ' (a_k:ℝ) (2*k) at mvt2,
      have h3 : |f k (1:ℝ)| = |f k (1:ℝ) - f k a_k + f k a_k| := by ring,
      have h4 : |f k (1:ℝ)| ≤ (1:ℝ) - a_k + a_k^(2*k+1) :=
        by linarith [abs_add (f k (1:ℝ) - f k a_k) (f k a_k), add_le_add mvt1 mvt2],
      have h5 : ((k:nnreal) ^ (-1/(2*(k:ℝ)+1))) ^ (2*(k:ℝ)+1) = k⁻¹,
      { rw [← nnreal.rpow_mul k (-1/(2*(k:ℝ)+1)) (2*(k:ℝ)+1), div_mul_cancel, nnreal.rpow_neg_one k],
        norm_cast, linarith },
      have h6 : 1/(k:ℝ) = (((k⁻¹):nnreal):ℝ) := by simp,
      convert h4,
      simp only [w, a_k],
      simp only [h6, ← h5], -- SHOULD BE ABLE TO COMBINE WITH ABOVE LINE
      norm_cast },
    intro k,
    rw ← norm_neg,
    convert f_bound k,
    simp [f, arctan_one, neg_sub, g, b] },
  rw [tendsto_iff_norm_tendsto_zero, ← tendsto_zero_iff_norm_tendsto_zero],
  refine squeeze_zero_norm H _,
  convert (tendsto.const_add (1:ℝ) (((tendsto_rpow_of_div_mul_add (-1) 2 1 (by norm_num)).neg).add
    tendsto_inv_at_top_zero)).comp tendsto_coe_nat_real_at_top_at_top,
  { ext k, simp only [w, one_div, nnreal.coe_nat_cast, nnreal.coe_rpow], ring },
  { simp },
end

end real
