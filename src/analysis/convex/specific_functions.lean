/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import analysis.special_functions.pow_deriv
import analysis.special_functions.sqrt

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

/-- `exp` is strictly convex on the whole real line. -/
lemma strict_convex_on_exp : strict_convex_on ℝ univ exp :=
strict_convex_on_univ_of_deriv2_pos continuous_exp (λ x, (iter_deriv_exp 2).symm ▸ exp_pos x)

/-- `exp` is convex on the whole real line. -/
lemma convex_on_exp : convex_on ℝ univ exp := strict_convex_on_exp.convex_on

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
lemma even.convex_on_pow {n : ℕ} (hn : even n) : convex_on ℝ set.univ (λ x : ℝ, x^n) :=
begin
  apply convex_on_univ_of_deriv2_nonneg (differentiable_pow n),
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
  apply strict_mono.strict_convex_on_univ_of_deriv (continuous_pow n),
  rw deriv_pow',
  replace h := nat.pos_of_ne_zero h,
  exact strict_mono.const_mul (odd.strict_mono_pow $ nat.even.sub_odd h hn $ nat.odd_iff.2 rfl)
    (nat.cast_pos.2 h),
end

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
lemma convex_on_pow (n : ℕ) : convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).continuous_on
    (differentiable_on_pow n),
  { simp only [deriv_pow'], exact (@differentiable_on_pow ℝ _ _ _).const_mul (n : ℝ) },
  { intros x hx,
    rw [iter_deriv_pow, finset.prod_range_cast_nat_sub],
    exact mul_nonneg (nat.cast_nonneg _) (pow_nonneg (interior_subset hx) _) }
end

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
lemma strict_convex_on_pow {n : ℕ} (hn : 2 ≤ n) : strict_convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply strict_mono_on.strict_convex_on_of_deriv (convex_Ici _) (continuous_on_pow _),
  rw [deriv_pow', interior_Ici],
  exact λ x (hx : 0 < x) y hy hxy, mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_left hxy hx.le $
    nat.sub_pos_of_lt hn) (nat.cast_pos.2 $ zero_lt_two.trans_le hn),
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
    rw iter_deriv_zpow,
    refine mul_nonneg _ (zpow_nonneg (le_of_lt hx) _),
    exact_mod_cast int_prod_range_nonneg _ _ (even_bit0 1) }
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
  rw interior_Ici,
  rintro x (hx : 0 < x),
  suffices : 0 < p * ((p - 1) * x ^ (p - 1 - 1)), by simpa [ne_of_gt hx, A],
  exact mul_pos (zero_lt_one.trans hp) (mul_pos (sub_pos_of_lt hp) (rpow_pos_of_pos hx _)),
end

lemma strict_concave_on_log_Ioi : strict_concave_on ℝ (Ioi 0) log :=
begin
  have h₁ : Ioi 0 ⊆ ({0} : set ℝ)ᶜ,
  { exact λ x (hx : 0 < x) (hx' : x = 0), hx.ne' hx' },
  refine strict_concave_on_of_deriv2_neg' (convex_Ioi 0)
    (continuous_on_log.mono h₁) (λ x (hx : 0 < x), _),
  rw [function.iterate_succ, function.iterate_one],
  change (deriv (deriv log)) x < 0,
  rw [deriv_log', deriv_inv],
  exact neg_neg_of_pos (inv_pos.2 $ sq_pos_of_ne_zero _ hx.ne'),
end

lemma strict_concave_on_log_Iio : strict_concave_on ℝ (Iio 0) log :=
begin
  have h₁ : Iio 0 ⊆ ({0} : set ℝ)ᶜ,
  { exact λ x (hx : x < 0) (hx' : x = 0), hx.ne hx' },
  refine strict_concave_on_of_deriv2_neg' (convex_Iio 0)
    (continuous_on_log.mono h₁) (λ x (hx : x < 0), _),
  rw [function.iterate_succ, function.iterate_one],
  change (deriv (deriv log)) x < 0,
  rw [deriv_log', deriv_inv],
  exact neg_neg_of_pos (inv_pos.2 $ sq_pos_of_ne_zero _ hx.ne),
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
