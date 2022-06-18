/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import analysis.calculus.mean_value
import analysis.special_functions.pow_deriv

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
open_locale big_operators

/-- `exp` is strictly convex on the whole real line. -/
lemma strict_convex_on_exp : strict_convex_on ℝ univ exp :=
strict_convex_on_univ_of_deriv2_pos differentiable_exp (λ x, (iter_deriv_exp 2).symm ▸ exp_pos x)

/-- `exp` is convex on the whole real line. -/
lemma convex_on_exp : convex_on ℝ univ exp := strict_convex_on_exp.convex_on

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
lemma even.convex_on_pow {n : ℕ} (hn : even n) : convex_on ℝ set.univ (λ x : ℝ, x^n) :=
begin
  apply convex_on_univ_of_deriv2_nonneg differentiable_pow,
  { simp only [deriv_pow', differentiable.mul, differentiable_const, differentiable_pow] },
  { intro x,
    obtain ⟨k, hk⟩ := (hn.tsub $ even_bit0 _).exists_two_nsmul _,
    rw [iter_deriv_pow, finset.prod_range_cast_nat_sub, hk, nsmul_eq_mul, pow_mul'],
    exact mul_nonneg (nat.cast_nonneg _) (pow_two_nonneg _) }
end

/-- `x^n`, `n : ℕ` is strictly convex on the whole real line whenever `n ≠ 0` is even. -/
lemma even.strict_convex_on_pow {n : ℕ} (hn : even n) (h : n ≠ 0) :
  strict_convex_on ℝ set.univ (λ x : ℝ, x^n) :=
begin
  apply strict_mono.strict_convex_on_univ_of_deriv differentiable_pow,
  rw deriv_pow',
  replace h := nat.pos_of_ne_zero h,
  exact strict_mono.const_mul (odd.strict_mono_pow $ nat.even.sub_odd h hn $ nat.odd_iff.2 rfl)
    (nat.cast_pos.2 h),
end

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
lemma convex_on_pow (n : ℕ) : convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).continuous_on
    differentiable_on_pow,
  { simp only [deriv_pow'], exact (@differentiable_on_pow ℝ _ _ _).const_mul (n : ℝ) },
  { intros x hx,
    rw [iter_deriv_pow, finset.prod_range_cast_nat_sub],
    exact mul_nonneg (nat.cast_nonneg _) (pow_nonneg (interior_subset hx) _) }
end

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
lemma strict_convex_on_pow {n : ℕ} (hn : 2 ≤ n) : strict_convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply strict_mono_on.strict_convex_on_of_deriv (convex_Ici _) (continuous_on_pow _)
    differentiable_on_pow,
  rw [deriv_pow', interior_Ici],
  exact λ x (hx : 0 < x) y hy hxy, mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_left hxy hx.le $
    nat.sub_pos_of_lt hn) (nat.cast_pos.2 $ zero_lt_two.trans_le hn),
end

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
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) (sub_nonpos_of_le this) },
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

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
lemma convex_on_zpow (m : ℤ) : convex_on ℝ (Ioi 0) (λ x : ℝ, x^m) :=
begin
  have : ∀ n : ℤ, differentiable_on ℝ (λ x, x ^ n) (Ioi (0 : ℝ)),
    from λ n, differentiable_on_zpow _ _ (or.inl $ lt_irrefl _),
  apply convex_on_of_deriv2_nonneg (convex_Ioi 0);
    try { simp only [interior_Ioi, deriv_zpow'] },
  { exact (this _).continuous_on },
  { exact this _ },
  { exact (this _).const_mul _ },
  { intros x hx,
    simp only [iter_deriv_zpow, ← int.cast_coe_nat, ← int.cast_sub, ← int.cast_prod],
    refine mul_nonneg (int.cast_nonneg.2 _) (zpow_nonneg (le_of_lt hx) _),
    exact int_prod_range_nonneg _ _ (even_bit0 1) }
end

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` except `0` and `1`. -/
lemma strict_convex_on_zpow {m : ℤ} (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) :
  strict_convex_on ℝ (Ioi 0) (λ x : ℝ, x^m) :=
begin
  have : ∀ n : ℤ, differentiable_on ℝ (λ x, x ^ n) (Ioi (0 : ℝ)),
    from λ n, differentiable_on_zpow _ _ (or.inl $ lt_irrefl _),
  apply strict_convex_on_of_deriv2_pos (convex_Ioi 0),
  { exact (this _).continuous_on },
   all_goals { rw interior_Ioi },
  { exact this _ },
  intros x hx,
  simp only [iter_deriv_zpow, ← int.cast_coe_nat, ← int.cast_sub, ← int.cast_prod],
  refine mul_pos (int.cast_pos.2 _) (zpow_pos_of_pos hx _),
  refine int_prod_range_pos (even_bit0 1) (λ hm, _),
  norm_cast at hm,
  rw ←finset.coe_Ico at hm,
  fin_cases hm,
  { exact hm₀ rfl },
  { exact hm₁ rfl }
end

lemma convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on ℝ (Ici 0) (λ x : ℝ, x^p) :=
begin
  have A : deriv (λ (x : ℝ), x ^ p) = λ x, p * x^(p-1), by { ext x, simp [hp] },
  apply convex_on_of_deriv2_nonneg (convex_Ici 0),
  { exact continuous_on_id.rpow_const (λ x _, or.inr (zero_le_one.trans hp)) },
  { exact (differentiable_rpow_const hp).differentiable_on },
  { rw A,
    assume x hx,
    replace hx : x ≠ 0, by { simp at hx, exact ne_of_gt hx },
    simp [differentiable_at.differentiable_within_at, hx] },
  { assume x hx,
    replace hx : 0 < x, by simpa using hx,
    suffices : 0 ≤ p * ((p - 1) * x ^ (p - 1 - 1)), by simpa [ne_of_gt hx, A],
    apply mul_nonneg (le_trans zero_le_one hp),
    exact mul_nonneg (sub_nonneg_of_le hp) (rpow_nonneg_of_nonneg hx.le _) }
end

lemma strict_convex_on_rpow {p : ℝ} (hp : 1 < p) : strict_convex_on ℝ (Ici 0) (λ x : ℝ, x^p) :=
begin
  have A : deriv (λ (x : ℝ), x ^ p) = λ x, p * x^(p-1), by { ext x, simp [hp.le] },
  apply strict_convex_on_of_deriv2_pos (convex_Ici 0),
  { exact continuous_on_id.rpow_const (λ x _, or.inr (zero_le_one.trans hp.le)) },
  { exact (differentiable_rpow_const hp.le).differentiable_on },
  rw interior_Ici,
  rintro x (hx : 0 < x),
  suffices : 0 < p * ((p - 1) * x ^ (p - 1 - 1)), by simpa [ne_of_gt hx, A],
  exact mul_pos (zero_lt_one.trans hp) (mul_pos (sub_pos_of_lt hp) (rpow_pos_of_pos hx _)),
end

lemma strict_concave_on_log_Ioi : strict_concave_on ℝ (Ioi 0) log :=
begin
  have h₁ : Ioi 0 ⊆ ({0} : set ℝ)ᶜ,
  { exact λ x (hx : 0 < x) (hx' : x = 0), hx.ne' hx' },
  refine strict_concave_on_open_of_deriv2_neg (convex_Ioi 0) is_open_Ioi
    (differentiable_on_log.mono h₁) (λ x (hx : 0 < x), _),
  rw [function.iterate_succ, function.iterate_one],
  change (deriv (deriv log)) x < 0,
  rw [deriv_log', deriv_inv],
  exact neg_neg_of_pos (inv_pos.2 $ sq_pos_of_ne_zero _ hx.ne'),
end

lemma strict_concave_on_log_Iio : strict_concave_on ℝ (Iio 0) log :=
begin
  have h₁ : Iio 0 ⊆ ({0} : set ℝ)ᶜ,
  { exact λ x (hx : x < 0) (hx' : x = 0), hx.ne hx' },
  refine strict_concave_on_open_of_deriv2_neg (convex_Iio 0) is_open_Iio
    (differentiable_on_log.mono h₁) (λ x (hx : x < 0), _),
  rw [function.iterate_succ, function.iterate_one],
  change (deriv (deriv log)) x < 0,
  rw [deriv_log', deriv_inv],
  exact neg_neg_of_pos (inv_pos.2 $ sq_pos_of_ne_zero _ hx.ne),
end

open_locale real

lemma strict_concave_on_sin_Icc : strict_concave_on ℝ (Icc 0 π) sin :=
begin
  apply strict_concave_on_of_deriv2_neg (convex_Icc _ _) continuous_on_sin
    differentiable_sin.differentiable_on (λ x hx, _),
  rw interior_Icc at hx,
  simp [sin_pos_of_mem_Ioo hx],
end

lemma strict_concave_on_cos_Icc : strict_concave_on ℝ (Icc (-(π/2)) (π/2)) cos :=
begin
  apply strict_concave_on_of_deriv2_neg (convex_Icc _ _) continuous_on_cos
    differentiable_cos.differentiable_on (λ x hx, _),
  rw interior_Icc at hx,
  simp [cos_pos_of_mem_Ioo hx],
end
