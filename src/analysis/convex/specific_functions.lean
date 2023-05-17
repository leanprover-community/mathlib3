/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import analysis.special_functions.pow.deriv
import analysis.special_functions.sqrt
import tactic.linear_combination

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `strict_convex_on_exp` : The exponential function is strictly convex.
* `even.convex_on_pow`, `even.strict_convex_on_pow` : For an even `n : ℕ`, `λ x, x ^ n` is convex
  and strictly convex when `2 ≤ n`.
* `convex_on_pow`, `strict_convex_on_pow` : For `n : ℕ`, `λ x, x ^ n` is convex on $[0, +∞)$ and
  strictly convex when `2 ≤ n`.
* `convex_on_zpow`, `strict_convex_on_zpow` : For `m : ℤ`, `λ x, x ^ m` is convex on $[0, +∞)$ and
  strictly convex when `m ≠ 0, 1`.
* `convex_on_rpow`, `strict_convex_on_rpow` : For `p : ℝ`, `λ x, x ^ p` is convex on $[0, +∞)$ when
  `1 ≤ p` and strictly convex when `1 < p`.
* `strict_concave_on_log_Ioi`, `strict_concave_on_log_Iio`: `real.log` is strictly concave on
  $(0, +∞)$ and $(-∞, 0)$ respectively.

## TODO

For `p : ℝ`, prove that `λ x, x ^ p` is concave when `0 ≤ p ≤ 1` and strictly concave when
`0 < p < 1`.
-/

open real set
open_locale big_operators nnreal

/-- `exp` is strictly convex on the whole real line.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
lemma strict_convex_on_exp : strict_convex_on ℝ univ exp :=
begin
  apply strict_convex_on_of_slope_strict_mono_adjacent convex_univ,
  rintros x y z - - hxy hyz,
  transitivity exp y,
  { have h1 : 0 < y - x := by linarith,
    have h2 : x - y < 0 := by linarith,
    rw div_lt_iff h1,
    calc exp y - exp x = exp y - exp y * exp (x - y) : by rw ← exp_add; ring_nf
    ... = exp y * (1 - exp (x - y)) : by ring
    ... < exp y * (-(x - y)) : mul_lt_mul_of_pos_left _ y.exp_pos
    ... = exp y * (y - x) : by ring,
    linarith [add_one_lt_exp_of_nonzero h2.ne] },
  { have h1 : 0 < z - y := by linarith,
    rw lt_div_iff h1,
    calc exp y * (z - y) < exp y * (exp (z - y) - 1) : mul_lt_mul_of_pos_left _ y.exp_pos
    ... = exp (z - y) * exp y - exp y : by ring
    ... ≤ exp z - exp y : by rw ← exp_add; ring_nf,
    linarith [add_one_lt_exp_of_nonzero h1.ne'] },
end

/-- `exp` is convex on the whole real line. -/
lemma convex_on_exp : convex_on ℝ univ exp := strict_convex_on_exp.convex_on

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n`.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
lemma convex_on_pow (n : ℕ) : convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  induction n with k IH,
  { exact convex_on_const (1:ℝ) (convex_Ici _) },
  refine ⟨convex_Ici _, _⟩,
  rintros a (ha : 0 ≤ a) b (hb : 0 ≤ b) μ ν hμ hν h,
  have H := IH.2 ha hb hμ hν h,
  have : 0 ≤ (b ^ k - a ^ k) * (b - a) * μ * ν,
  { cases le_or_lt a b with hab hab,
    { have : a ^ k ≤ b ^ k := pow_le_pow_of_le_left ha hab k,
      have : 0 ≤ (b ^ k - a ^ k) * (b - a) := by nlinarith,
      positivity, },
    { have : b ^ k ≤ a ^ k := pow_le_pow_of_le_left hb hab.le k,
      have : 0 ≤ (b ^ k - a ^ k) * (b - a) := by nlinarith,
      positivity, } },
  calc (μ * a + ν * b) ^ k.succ = (μ * a + ν * b) * (μ * a + ν * b) ^ k : by ring_exp
  ... ≤ (μ * a + ν * b) * (μ * a ^ k + ν * b ^ k) : mul_le_mul_of_nonneg_left H (by positivity)
  ... ≤ (μ * a + ν * b) * (μ * a ^ k + ν * b ^ k) + (b ^ k - a ^ k) * (b - a) * μ * ν : by linarith
  ... = (μ + ν) * (μ * a ^ k.succ + ν * b ^ k.succ) : by ring_exp
  ... = μ * a ^ k.succ + ν * b ^ k.succ : by rw h; ring_exp,
end

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
lemma strict_convex_on_pow {n : ℕ} (hn : 2 ≤ n) : strict_convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply strict_mono_on.strict_convex_on_of_deriv (convex_Ici _) (continuous_on_pow _),
  rw [deriv_pow', interior_Ici],
  exact λ x (hx : 0 < x) y hy hxy, mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_left hxy hx.le $
    nat.sub_pos_of_lt hn) (nat.cast_pos.2 $ zero_lt_two.trans_le hn),
end

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
lemma even.convex_on_pow {n : ℕ} (hn : even n) : convex_on ℝ set.univ (λ x : ℝ, x^n) :=
begin
  refine ⟨convex_univ, _⟩,
  intros a ha b hb μ ν hμ hν h,
  obtain ⟨k, rfl⟩ := hn.exists_two_nsmul _,
  have : 0 ≤ (a - b) ^ 2 * μ * ν := by positivity,
  calc (μ * a + ν * b) ^ (2 * k) = ((μ * a + ν * b) ^ 2) ^ k : by rw pow_mul
  ... ≤ ((μ + ν) * (μ * a ^ 2 + ν * b ^ 2)) ^ k : pow_le_pow_of_le_left (by positivity) _ k
  ... = (μ * a ^ 2 + ν * b ^ 2) ^ k : by rw h; ring_exp
  ... ≤ μ * (a ^ 2) ^ k + ν * (b ^ 2) ^ k : _
  ... ≤ μ * a ^ (2 * k) + ν * b ^ (2 * k) : by ring_exp,
  { linarith },
  { refine (convex_on_pow k).2 _ _ hμ hν h; dsimp; positivity },
end

/-- `x^n`, `n : ℕ` is strictly convex on the whole real line whenever `n ≠ 0` is even. -/
lemma even.strict_convex_on_pow {n : ℕ} (hn : even n) (h : n ≠ 0) :
  strict_convex_on ℝ set.univ (λ x : ℝ, x^n) :=
begin
  apply strict_mono.strict_convex_on_univ_of_deriv (continuous_pow n),
  rw deriv_pow',
  replace h := nat.pos_of_ne_zero h,
  exact strict_mono.const_mul (odd.strict_mono_pow $ nat.even.sub_odd h hn $ nat.odd_iff.2 rfl)
    (nat.cast_pos.2 h),
end

/-- Specific case of Jensen's inequality for sums of powers -/
lemma real.pow_sum_div_card_le_sum_pow {α : Type*} {s : finset α} {f : α → ℝ} (n : ℕ)
  (hf : ∀ a ∈ s, 0 ≤ f a) : (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, (f x) ^ (n + 1) :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hs,
  { simp_rw [finset.sum_empty, zero_pow' _ (nat.succ_ne_zero n), zero_div] },
  { have hs0 : 0 < (s.card : ℝ) := nat.cast_pos.2 hs.card_pos,
    suffices : (∑ x in s, f x / s.card) ^ (n + 1) ≤ ∑ x in s, (f x ^ (n + 1) / s.card),
    { rwa [← finset.sum_div, ← finset.sum_div, div_pow, pow_succ' (s.card : ℝ),
        ← div_div, div_le_iff hs0, div_mul, div_self hs0.ne', div_one] at this },
    have := @convex_on.map_sum_le ℝ ℝ ℝ α _ _ _ _ _ _ (set.Ici 0) (λ x, x ^ (n + 1)) s
      (λ _, 1 / s.card) (coe ∘ f) (convex_on_pow (n + 1)) _ _ (λ i hi, set.mem_Ici.2 (hf i hi)),
    { simpa only [inv_mul_eq_div, one_div, algebra.id.smul_eq_mul] using this },
    { simp only [one_div, inv_nonneg, nat.cast_nonneg, implies_true_iff] },
    { simpa only [one_div, finset.sum_const, nsmul_eq_mul] using mul_inv_cancel hs0.ne' } }
end

lemma nnreal.pow_sum_div_card_le_sum_pow {α : Type*} (s : finset α) (f : α → ℝ≥0) (n : ℕ) :
  (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, (f x) ^ (n + 1) :=
by simpa only [← nnreal.coe_le_coe, nnreal.coe_sum, nonneg.coe_div, nnreal.coe_pow] using
  @real.pow_sum_div_card_le_sum_pow α s (coe ∘ f) n (λ _ _, nnreal.coe_nonneg _)

lemma finset.prod_nonneg_of_card_nonpos_even
  {α β : Type*} [linear_ordered_comm_ring β]
  {f : α → β} [decidable_pred (λ x, f x ≤ 0)]
  {s : finset α} (h0 : even (s.filter (λ x, f x ≤ 0)).card) :
  0 ≤ ∏ x in s, f x :=
calc 0 ≤ (∏ x in s, ((if f x ≤ 0 then (-1:β) else 1) * f x)) :
  finset.prod_nonneg (λ x _, by
    { split_ifs with hx hx, by simp [hx], simp at hx ⊢, exact le_of_lt hx })
... = _ : by rw [finset.prod_mul_distrib, finset.prod_ite, finset.prod_const_one,
  mul_one, finset.prod_const, neg_one_pow_eq_pow_mod_two, nat.even_iff.1 h0, pow_zero, one_mul]

lemma int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : even n) :
  0 ≤ ∏ k in finset.range n, (m - k) :=
begin
  rcases hn with ⟨n, rfl⟩,
  induction n with n ihn, { simp },
  rw ← two_mul at ihn,
  rw [← two_mul, nat.succ_eq_add_one, mul_add, mul_one, bit0, ← add_assoc, finset.prod_range_succ,
    finset.prod_range_succ, mul_assoc],
  refine mul_nonneg ihn _, generalize : (1 + 1) * n = k,
  cases le_or_lt m k with hmk hmk,
  { have : m ≤ k + 1, from hmk.trans (lt_add_one ↑k).le,
    convert mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _,
    convert sub_nonpos_of_le this },
  { exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk) }
end

lemma int_prod_range_pos {m : ℤ} {n : ℕ} (hn : even n) (hm : m ∉ Ico (0 : ℤ) n) :
  0 < ∏ k in finset.range n, (m - k) :=
begin
  refine (int_prod_range_nonneg m n hn).lt_of_ne (λ h, hm _),
  rw [eq_comm, finset.prod_eq_zero_iff] at h,
  obtain ⟨a, ha, h⟩ := h,
  rw sub_eq_zero.1 h,
  exact ⟨int.coe_zero_le _, int.coe_nat_lt.2 $ finset.mem_range.1 ha⟩,
end

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m`.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
lemma convex_on_zpow : ∀ m : ℤ, convex_on ℝ (Ioi 0) (λ x : ℝ, x^m)
| (n : ℕ) :=
begin
  simp_rw zpow_coe_nat,
  exact (convex_on_pow n).subset Ioi_subset_Ici_self (convex_Ioi _)
end
| -[1+ n] :=
begin
  simp_rw zpow_neg_succ_of_nat,
  refine ⟨convex_Ioi _, _⟩,
  rintros a (ha : 0 < a) b (hb : 0 < b) μ ν hμ hν h,
  have ha' : 0 < a ^ (n + 1) := by positivity,
  have hb' : 0 < b ^ (n + 1) := by positivity,
  field_simp [ha.ne', hb.ne', ha'.ne', hb'.ne'],
  rw div_le_div_iff,
  { calc 1 * (a ^ (n + 1) * b ^ (n + 1))
        = ((μ + ν) ^ 2 * (a * b)) ^ (n + 1) : by rw h; ring_exp
    ... ≤ ((μ * b + ν * a) * (μ * a + ν * b)) ^ (n + 1) : pow_le_pow_of_le_left _ _ _
    ... = (μ * b + ν * a) ^ (n + 1) * (μ * a + ν * b) ^ (n + 1) : by rw mul_pow
    ... ≤ (μ * b ^ (n + 1) + ν * a ^ (n + 1)) * (μ * a + ν * b) ^ (n + 1) : _,
    { positivity },
    { have : 0 ≤ μ * ν * (a - b) ^ 2 := by positivity,
      linarith },
    { apply mul_le_mul_of_nonneg_right ((convex_on_pow (n + 1)).2 hb.le ha.le hμ hν h),
      positivity } },
  { have : 0 < μ * a + ν * b := by cases le_or_lt a b; nlinarith,
    positivity },
  { positivity },
end

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` except `0` and `1`. -/
lemma strict_convex_on_zpow {m : ℤ} (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) :
  strict_convex_on ℝ (Ioi 0) (λ x : ℝ, x^m) :=
begin
  apply strict_convex_on_of_deriv2_pos' (convex_Ioi 0),
  { exact (continuous_on_zpow₀ m).mono (λ x hx, ne_of_gt hx) },
  intros x hx,
  rw iter_deriv_zpow,
  refine mul_pos _ (zpow_pos_of_pos hx _),
  exact_mod_cast int_prod_range_pos (even_bit0 1) (λ hm, _),
  norm_cast at hm,
  rw ← finset.coe_Ico at hm,
  fin_cases hm; cc,
end

/- `real.log` is strictly concave on $(0, +∞)$.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
lemma strict_concave_on_log_Ioi : strict_concave_on ℝ (Ioi 0) log :=
begin
  apply strict_concave_on_of_slope_strict_anti_adjacent (convex_Ioi (0:ℝ)),
  rintros x y z (hx : 0 < x) (hz : 0 < z) hxy hyz,
  have hy : 0 < y := hx.trans hxy,
  transitivity y⁻¹,
  { have h : 0 < z - y := by linarith,
    rw div_lt_iff h,
    have hyz' : 0 < z / y := by positivity,
    have hyz'' : z / y ≠ 1,
    { contrapose! h,
      rw div_eq_one_iff_eq hy.ne' at h,
      simp [h] },
    calc log z - log y = log (z / y) : by rw ← log_div hz.ne' hy.ne'
    ... < z / y - 1 : log_lt_sub_one_of_pos hyz' hyz''
    ... = y⁻¹ * (z - y) : by field_simp [hy.ne'] },
  { have h : 0 < y - x := by linarith,
    rw lt_div_iff h,
    have hxy' : 0 < x / y := by positivity,
    have hxy'' : x / y ≠ 1,
    { contrapose! h,
      rw div_eq_one_iff_eq hy.ne' at h,
      simp [h] },
    calc y⁻¹ * (y - x) = 1 - x / y : by field_simp [hy.ne']
    ... < - log (x / y) : by linarith [log_lt_sub_one_of_pos hxy' hxy'']
    ... = - (log x - log y) : by rw log_div hx.ne' hy.ne'
    ... = log y - log x : by ring },
end

/-- **Bernoulli's inequality** for real exponents, strict version: for `1 < p` and `-1 ≤ s`, with
`s ≠ 0`, we have `1 + p * s < (1 + s) ^ p`. -/
lemma one_add_mul_self_lt_rpow_one_add {s : ℝ} (hs : -1 ≤ s) (hs' : s ≠ 0) {p : ℝ} (hp : 1 < p) :
  1 + p * s < (1 + s) ^ p :=
begin
  rcases eq_or_lt_of_le hs with rfl | hs,
  { have : p ≠ 0 := by positivity,
    simpa [zero_rpow this], },
  have hs1 : 0 < 1 + s := by linarith,
  cases le_or_lt (1 + p * s) 0 with hs2 hs2,
  { exact hs2.trans_lt (rpow_pos_of_pos hs1 _) },
  rw [rpow_def_of_pos hs1, ← exp_log hs2],
  apply exp_strict_mono,
  have hp : 0 < p := by positivity,
  have hs3 : 1 + s ≠ 1 := by contrapose! hs'; linarith,
  have hs4 : 1 + p * s ≠ 1 := by contrapose! hs'; nlinarith,
  cases lt_or_gt_of_ne hs' with hs' hs',
  { rw [← div_lt_iff hp, ← div_lt_div_right_of_neg hs'],
    convert strict_concave_on_log_Ioi.secant_mono zero_lt_one hs2 hs1 hs4 hs3 _ using 1,
    { field_simp [log_one] },
    { field_simp [log_one] },
    { nlinarith } },
  { rw [← div_lt_iff hp, ← div_lt_div_right hs'],
    convert strict_concave_on_log_Ioi.secant_mono zero_lt_one hs1 hs2 hs3 hs4 _ using 1,
    { field_simp [log_one, hp.ne'], },
    { field_simp [log_one] },
    { nlinarith } },
end

/-- **Bernoulli's inequality** for real exponents, non-strict version: for `1 ≤ p` and `-1 ≤ s`
we have `1 + p * s ≤ (1 + s) ^ p`. -/
lemma one_add_mul_self_le_rpow_one_add {s : ℝ} (hs : -1 ≤ s) {p : ℝ} (hp : 1 ≤ p) :
  1 + p * s ≤ (1 + s) ^ p :=
begin
  rcases eq_or_lt_of_le hp with rfl | hp,
  { simp },
  by_cases hs' : s = 0,
  { simp [hs'] },
  exact (one_add_mul_self_lt_rpow_one_add hs hs' hp).le,
end

/- For `p : ℝ` with `1 < p`, `λ x, x ^ p` is strictly convex on $[0, +∞)$.

We give an elementary proof rather than using the second derivative test, since this lemma is
needed early in the analysis library. -/
lemma strict_convex_on_rpow {p : ℝ} (hp : 1 < p) : strict_convex_on ℝ (Ici 0) (λ x : ℝ, x^p) :=
begin
  apply strict_convex_on_of_slope_strict_mono_adjacent (convex_Ici (0:ℝ)),
  rintros x y z (hx : 0 ≤ x) (hz : 0 ≤ z) hxy hyz,
  have hy : 0 < y := by linarith,
  have hy' : 0 < y ^ p := rpow_pos_of_pos hy _,
  have H1 : y ^ ((p - 1) + 1) = y ^ (p - 1) * y := rpow_add_one hy.ne' _,
  ring_nf at H1,
  transitivity p * y ^ (p - 1),
  { have hyx' : x - y < 0 := by linarith only [hxy],
    have h3 : 0 < y - x := by linarith only [hxy],
    have hyx'' : x / y < 1 := by rwa div_lt_one hy,
    have hyx''' : x / y - 1 < 0 := by linarith only [hyx''],
    have hyx'''' : 0 ≤ x / y := by positivity,
    have hyx''''' : -1 ≤ x / y - 1 := by linarith only [hyx''''],
    have : 1 - (1 + ((x / y) - 1)) ^ p < - p * ((x / y) - 1),
    { linarith [one_add_mul_self_lt_rpow_one_add hyx''''' hyx'''.ne hp] },
    rw [div_lt_iff h3, ← div_lt_div_right hy'],
    convert this using 1,
    { have H : (x / y) ^ p = x ^ p / y ^ p := div_rpow hx hy.le _,
      ring_nf at ⊢ H,
      field_simp [hy.ne', hy'.ne'] at ⊢ H,
      linear_combination H },
    { field_simp [hy.ne', hy'.ne'],
      linear_combination p * (-y + x) * H1 }, },
  { have hyz' : 0 < z - y := by linarith only [hyz],
    have hyz'' : 1 < z / y := by rwa one_lt_div hy,
    have hyz''' : 0 < z / y - 1 := by linarith only [hyz''],
    have hyz'''' : -1 ≤ z / y - 1 := by linarith only [hyz''],
    have : p * ((z / y) - 1) < (1 + ((z / y) - 1)) ^ p - 1,
    { linarith [one_add_mul_self_lt_rpow_one_add hyz'''' hyz'''.ne' hp] },
    rw [lt_div_iff hyz', ← div_lt_div_right hy'],
    convert this using 1,
    { field_simp [hy.ne', hy'.ne'],
      linear_combination - p * (z - y) * H1, },
    { have H : (z / y) ^ p = z ^ p / y ^ p := div_rpow hz hy.le _,
      ring_nf at ⊢ H,
      field_simp [hy.ne', hy'.ne'] at ⊢ H,
      linear_combination -H } },
end

lemma convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on ℝ (Ici 0) (λ x : ℝ, x^p) :=
begin
  rcases eq_or_lt_of_le hp with rfl | hp,
  { simpa using convex_on_id (convex_Ici _), },
  exact (strict_convex_on_rpow hp).convex_on,
end

lemma strict_concave_on_log_Iio : strict_concave_on ℝ (Iio 0) log :=
begin
  refine ⟨convex_Iio _, _⟩,
  rintros x (hx : x < 0) y (hy : y < 0) hxy a b ha hb hab,
  have hx' : 0 < -x := by linarith,
  have hy' : 0 < -y := by linarith,
  have hxy' : - x ≠ - y := by contrapose! hxy; linarith,
  calc a • log x + b • log y = a • log (-x) + b • log (-y) : by simp_rw [log_neg_eq_log]
  ... < log (a • (-x) + b • (-y)) : strict_concave_on_log_Ioi.2 hx' hy' hxy' ha hb hab
  ... = log (- (a • x + b • y)) : by congr' 1; simp only [algebra.id.smul_eq_mul]; ring
  ... = _ : by rw log_neg_eq_log,
end

section sqrt_mul_log

lemma has_deriv_at_sqrt_mul_log {x : ℝ} (hx : x ≠ 0) :
  has_deriv_at (λ x, sqrt x * log x) ((2 + log x) / (2 * sqrt x)) x :=
begin
  convert (has_deriv_at_sqrt hx).mul (has_deriv_at_log hx),
  rw [add_div, div_mul_right (sqrt x) two_ne_zero, ←div_eq_mul_inv, sqrt_div_self',
      add_comm, div_eq_mul_one_div, mul_comm],
end

lemma deriv_sqrt_mul_log (x : ℝ) : deriv (λ x, sqrt x * log x) x = (2 + log x) / (2 * sqrt x) :=
begin
  cases lt_or_le 0 x with hx hx,
  { exact (has_deriv_at_sqrt_mul_log hx.ne').deriv },
  { rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero],
    refine has_deriv_within_at.deriv_eq_zero _ (unique_diff_on_Iic 0 x hx),
    refine (has_deriv_within_at_const x _ 0).congr_of_mem (λ x hx, _) hx,
    rw [sqrt_eq_zero_of_nonpos hx, zero_mul] },
end

lemma deriv_sqrt_mul_log' : deriv (λ x, sqrt x * log x) = λ x, (2 + log x) / (2 * sqrt x) :=
funext deriv_sqrt_mul_log

lemma deriv2_sqrt_mul_log (x : ℝ) :
  deriv^[2] (λ x, sqrt x * log x) x = -log x / (4 * sqrt x ^ 3) :=
begin
  simp only [nat.iterate, deriv_sqrt_mul_log'],
  cases le_or_lt x 0 with hx hx,
  { rw [sqrt_eq_zero_of_nonpos hx, zero_pow zero_lt_three, mul_zero, div_zero],
    refine has_deriv_within_at.deriv_eq_zero _ (unique_diff_on_Iic 0 x hx),
    refine (has_deriv_within_at_const _ _ 0).congr_of_mem (λ x hx, _) hx,
    rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero] },
  { have h₀ : sqrt x ≠ 0, from sqrt_ne_zero'.2 hx,
    convert (((has_deriv_at_log hx.ne').const_add 2).div
      ((has_deriv_at_sqrt hx.ne').const_mul 2) $ mul_ne_zero two_ne_zero h₀).deriv using 1,
    nth_rewrite 2 [← mul_self_sqrt hx.le],
    field_simp, ring },
end

lemma strict_concave_on_sqrt_mul_log_Ioi : strict_concave_on ℝ (set.Ioi 1) (λ x, sqrt x * log x) :=
begin
  apply strict_concave_on_of_deriv2_neg' (convex_Ioi 1) _ (λ x hx, _),
  { exact continuous_sqrt.continuous_on.mul
      (continuous_on_log.mono (λ x hx, ne_of_gt (zero_lt_one.trans hx))) },
  { rw [deriv2_sqrt_mul_log x],
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
      (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3)) },
end

end sqrt_mul_log

open_locale real

lemma strict_concave_on_sin_Icc : strict_concave_on ℝ (Icc 0 π) sin :=
begin
  apply strict_concave_on_of_deriv2_neg (convex_Icc _ _) continuous_on_sin (λ x hx, _),
  rw interior_Icc at hx,
  simp [sin_pos_of_mem_Ioo hx],
end

lemma strict_concave_on_cos_Icc : strict_concave_on ℝ (Icc (-(π/2)) (π/2)) cos :=
begin
  apply strict_concave_on_of_deriv2_neg (convex_Icc _ _) continuous_on_cos (λ x hx, _),
  rw interior_Icc at hx,
  simp [cos_pos_of_mem_Ioo hx],
end
