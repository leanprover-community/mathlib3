import analysis.exponential

universe u

lemma lt_mul_of_div_lt {α : Type u} [linear_ordered_field α] {a b c : α} (hc : c > 0)
  (h : a / c < b) : a < b * c :=
calc
   a = a / c * c : by rw [div_mul_cancel _ $ (ne_of_lt hc).symm]
 ... < b * c     : mul_lt_mul_of_pos_right h hc

lemma pow_lt_pow {α : Type u} [linear_ordered_semiring α] {a : α} {n m : ℕ}
  (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
begin
  have h' : 1 ≤ a := le_of_lt h,
  have h'' : 0 < a := lt_trans zero_lt_one h,
  cases m, cases h2, rw [pow_succ, ←one_mul (a ^ n)],
  exact mul_lt_mul h (pow_le_pow h' (nat.le_of_lt_succ h2)) (pow_pos h'' _) (le_of_lt h'')
end

namespace real
variable (x : ℝ)

lemma sqrt_le_sqrt {x y : ℝ} (h : x ≤ y) : sqrt x ≤ sqrt y :=
begin
  rw [mul_self_le_mul_self_iff (sqrt_nonneg _) (sqrt_nonneg _), (sqrt_prop _).2, (sqrt_prop _).2],
  exact max_le_max (le_refl _) h
end

lemma sqrt_le_left {x y : ℝ} (hy : 0 ≤ y) : sqrt x ≤ y ↔ x ≤ y ^ 2 :=
begin
  rw [mul_self_le_mul_self_iff (sqrt_nonneg _) hy, pow_two],
  cases le_total 0 x with hx hx,
  { rw [mul_self_sqrt hx] },
  { have h1 : 0 ≤ y * y := mul_nonneg hy hy,
    have h2 : x ≤ y * y := le_trans hx h1,
    simp [sqrt_eq_zero_of_nonpos, hx, h1, h2] }
end

/- note: if you want to conclude `x ≤ sqrt y`, then use `le_sqrt_of_sqr_le`.
   if you have `y > 0`, consider using `le_sqrt'` -/
lemma le_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
by rw [mul_self_le_mul_self_iff hx (sqrt_nonneg _), pow_two, mul_self_sqrt hy]

lemma le_sqrt' {x y : ℝ} (hx : 0 < x) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
begin
  rw [mul_self_le_mul_self_iff (le_of_lt hx) (sqrt_nonneg _), pow_two],
  cases le_total 0 y with hy hy,
  { rw [mul_self_sqrt hy] },
  { have h1 : 0 < x * x := mul_pos hx hx,
    have h2 : ¬x * x ≤ y := not_le_of_lt (lt_of_le_of_lt hy h1),
    simp [sqrt_eq_zero_of_nonpos, hy, h1, h2] }
end

lemma le_sqrt_of_sqr_le {x y : ℝ} (h : x ^ 2 ≤ y) : x ≤ sqrt y :=
begin
  cases lt_or_ge 0 x with hx hx,
  { rwa [le_sqrt' hx] },
  { exact le_trans hx (sqrt_nonneg y) }
end

lemma div_lt_self {x y : ℝ} (hx : x > 0) (hy : y > 1) : x / y < x :=
by simpa using div_lt_div' (le_refl x) hy hx zero_lt_one

lemma cos_square : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
by simp [cos_two_mul, div_add_div_same, mul_div_cancel_left, two_ne_zero, -one_div_eq_inv]

lemma sin_square : sin x ^ 2 = 1 - cos x ^ 2 :=
by { rw [←sin_pow_two_add_cos_pow_two x], simp }

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

lemma sqrt_two_add_series_step_up {x z : ℝ} {n : ℕ} (y : ℝ) (hz : sqrt_two_add_series y n ≤ z)
  (h : 2 + x ≤ y ^ 2) (h2 : 0 ≤ y) : sqrt_two_add_series x (n+1) ≤ z :=
begin
  refine le_trans _ hz, rw [sqrt_two_add_series_succ], apply sqrt_two_add_series_monotone_left,
  rw [sqrt_le_left], exact h, exact h2
end

lemma sqrt_two_add_series_step_down {x z : ℝ} {n : ℕ} (y : ℝ) (hz : z ≤ sqrt_two_add_series y n)
  (h : y ^ 2 ≤ 2 + x) : z ≤ sqrt_two_add_series x (n+1) :=
begin
  apply le_trans hz, rw [sqrt_two_add_series_succ],
  apply sqrt_two_add_series_monotone_left, exact le_sqrt_of_sqr_le h
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
  apply div_lt_self pi_pos,
  refine lt_of_le_of_lt (le_of_eq (pow_zero 2).symm) _,
  apply pow_lt_pow, norm_num, apply nat.succ_pos, norm_num, norm_num
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

lemma sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
begin
  cases le_or_gt x 1 with h' h',
  { have hx : abs x = x := abs_of_nonneg (le_of_lt h),
    have : abs x ≤ 1, rwa [hx],
    have := sin_bound this, rw [abs_le] at this,
    have := this.2, rw [sub_le_iff_le_add', hx] at this,
    apply lt_of_le_of_lt this, rw [sub_add], apply lt_of_lt_of_le _ (le_of_eq (sub_zero x)),
    apply sub_lt_sub_left, rw sub_pos, apply mul_lt_mul',
    { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
      rw mul_le_mul_right, exact h', apply pow_pos h },
    norm_num, norm_num, apply pow_pos h },
  exact lt_of_le_of_lt (sin_le_one x) h'
end

/- note 1: this inequality is not tight, the tighter inequality is sin x > x - x ^ 3 / 6.
   note 2: this is also true for x > 1, but it's nontrivial for x just above 1. -/
lemma sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : sin x > x - x ^ 3 / 4 :=
begin
  have hx : abs x = x := abs_of_nonneg (le_of_lt h),
  have : abs x ≤ 1, rwa [hx],
  have := sin_bound this, rw [abs_le] at this,
  have := this.1, rw [le_sub_iff_add_le, hx] at this,
  refine lt_of_lt_of_le _ this,
  rw [add_comm, sub_add, sub_neg_eq_add], apply sub_lt_sub_left,
  apply add_lt_of_lt_sub_left,
  rw (show x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 / 12,
    by simp [div_eq_mul_inv, (mul_sub _ _ _).symm, -sub_eq_add_neg]; congr; norm_num),
  apply mul_lt_mul',
  { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
    rw mul_le_mul_right, exact h', apply pow_pos h },
  norm_num, norm_num, apply pow_pos h
end

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
  { apply lt_mul_of_div_lt, apply pow_pos, norm_num,
    rw [←sin_pi_over_two_pow_succ],
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
    convert le_refl _, norm_num, norm_num, apply pow_ne_zero, norm_num, norm_num },
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
  apply sqrt_two_add_series_step_up (23/16),
  all_goals {norm_num}
end

lemma pi_gt_314 : pi > 3.14 :=
begin
  refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series 4), rw [mul_comm],
  apply le_mul_of_div_le, norm_num, apply le_sqrt_of_sqr_le, rw [le_sub],
  apply sqrt_two_add_series_step_up (99/70),
  apply sqrt_two_add_series_step_up (874/473),
  apply sqrt_two_add_series_step_up (1940/989),
  apply sqrt_two_add_series_step_up (1447/727),
  all_goals {norm_num}
end

lemma pi_lt_315 : pi < 3.15 :=
begin
  refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series 4) _,
  apply add_le_of_le_sub_right, rw [mul_comm], apply mul_le_of_le_div, apply pow_pos, norm_num,
  rw [sqrt_le_left, sub_le], swap, norm_num,
  apply sqrt_two_add_series_step_down (140/99),
  apply sqrt_two_add_series_step_down (279/151),
  apply sqrt_two_add_series_step_down (51/26),
  apply sqrt_two_add_series_step_down (412/207),
  all_goals {norm_num}
end

-- -- the following lemma takes about 9 seconds
-- lemma pi_gt_31415 : pi > 3.1415 :=
-- begin
--   refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series 6), rw [mul_comm],
--   apply le_mul_of_div_le, norm_num, apply le_sqrt_of_sqr_le, rw [le_sub],
--   apply sqrt_two_add_series_step_up (11482/8119),
--   apply sqrt_two_add_series_step_up (5401/2923),
--   apply sqrt_two_add_series_step_up (2348/1197),
--   apply sqrt_two_add_series_step_up (11367/5711),
--   apply sqrt_two_add_series_step_up (25705/12868),
--   apply sqrt_two_add_series_step_up (23235/11621),
--   all_goals {norm_num}
-- end

-- -- the following lemma takes about 14 seconds
-- lemma pi_lt_31416 : pi < 3.1416 :=
-- begin
--   refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series 9) _,
--   apply add_le_of_le_sub_right, rw [mul_comm], apply mul_le_of_le_div, apply pow_pos, norm_num,
--   rw [sqrt_le_left, sub_le], swap, norm_num,
--   apply sqrt_two_add_series_step_down (4756/3363),
--   apply sqrt_two_add_series_step_down (101211/54775),
--   apply sqrt_two_add_series_step_down (505534/257719),
--   apply sqrt_two_add_series_step_down (83289/41846),
--   apply sqrt_two_add_series_step_down (411278/205887),
--   apply sqrt_two_add_series_step_down (438142/219137),
--   apply sqrt_two_add_series_step_down (451504/225769),
--   apply sqrt_two_add_series_step_down (265603/132804),
--   apply sqrt_two_add_series_step_down (849938/424971),
--   all_goals {norm_num}
-- end

-- -- the following lemma takes about 15 seconds
-- lemma pi_gt_3141592 : pi > 3.141592  :=
-- begin
--   refine lt_of_le_of_lt _ (pi_gt_sqrt_two_add_series 10), rw [mul_comm],
--   apply le_mul_of_div_le, norm_num, apply le_sqrt_of_sqr_le, rw [le_sub],
--   apply sqrt_two_add_series_step_up (11482/8119),
--   apply sqrt_two_add_series_step_up (7792/4217),
--   apply sqrt_two_add_series_step_up (54055/27557),
--   apply sqrt_two_add_series_step_up (949247/476920),
--   apply sqrt_two_add_series_step_up (3310126/1657059),
--   apply sqrt_two_add_series_step_up (2635492/1318143),
--   apply sqrt_two_add_series_step_up (1580265/790192),
--   apply sqrt_two_add_series_step_up (1221775/610899),
--   apply sqrt_two_add_series_step_up (3612247/1806132),
--   apply sqrt_two_add_series_step_up (849943/424972),
--   all_goals {norm_num}
-- end

-- the following lemma takes about 19 seconds
-- lemma pi_lt_3141593 : pi < 3.141593 :=
-- begin
--   refine lt_of_lt_of_le (pi_lt_sqrt_two_add_series 11) _,
--   apply add_le_of_le_sub_right, rw [mul_comm], apply mul_le_of_le_div, apply pow_pos, norm_num,
--   rw [sqrt_le_left, sub_le], swap, norm_num,
--   apply sqrt_two_add_series_step_down (27720/19601),
--   apply sqrt_two_add_series_step_down (56935/30813),
--   apply sqrt_two_add_series_step_down (49359/25163),
--   apply sqrt_two_add_series_step_down (258754/130003),
--   apply sqrt_two_add_series_step_down (113599/56868),
--   apply sqrt_two_add_series_step_down (1101994/551163),
--   apply sqrt_two_add_series_step_down (8671537/4336095),
--   apply sqrt_two_add_series_step_down (3877807/1938940),
--   apply sqrt_two_add_series_step_down (52483813/26242030),
--   apply sqrt_two_add_series_step_down (56946167/28473117),
--   apply sqrt_two_add_series_step_down (23798415/11899211),
--   all_goals {norm_num},
-- end


end real

/- why is division_ring.inv_inj in the file "field"?-/


-- namespace complex
-- variable (x : ℂ)

-- lemma cos_square : cos x ^ 2 = (1 + cos (2 * x)) / 2 :=
-- by simp [cos_two_mul, mul_div_cancel_left, two_ne_zero']

-- @[simp] lemma div_re (z w : ℂ) : (z / w).re = z.re * w.re / norm_sq w + z.im * w.im / norm_sq w :=
-- by simp [div_eq_mul_inv, mul_assoc]

-- end complex

-- lemma one_add_div {x y : ℝ} (h : y ≠ 0) : 1 + x / y = (y + x) / y :=
-- by rw [←div_self h, div_add_div_same]

-- lemma one_add_neg_div {x y : ℝ} (h : y ≠ 0) : 1 + -(x / y) = (y - x) / y :=
-- by rw [←div_self h, ← sub_eq_add_neg, div_sub_div_same]
