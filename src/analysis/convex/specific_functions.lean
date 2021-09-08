/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import analysis.calculus.mean_value
import analysis.special_functions.pow

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `convex_on_exp` : the exponential function is convex on $(-∞, +∞)$;
* `convex_on_pow_of_even` : given an even natural number $n$, the function $f(x)=x^n$
  is convex on $(-∞, +∞)$;
* `convex_on_pow` : for a natural $n$, the function $f(x)=x^n$ is convex on $[0, +∞)$;
* `convex_on_fpow` : for an integer $m$, the function $f(x)=x^m$ is convex on $(0, +∞)$.
* `convex_on_rpow : ∀ p : ℝ, 1 ≤ p → convex_on 𝕜 (Ici 0) (λ x, x ^ p)`
* `concave_on_log_Ioi` and `concave_on_log_Iio`: log is concave on `Ioi 0` and `Iio 0` respectively.
-/

open real set
open_locale big_operators

/-- `exp` is convex on the whole real line -/
lemma convex_on_exp : convex_on 𝕜 univ exp :=
convex_on_univ_of_deriv2_nonneg differentiable_exp (by simp)
  (assume x, (iter_deriv_exp 2).symm ▸ le_of_lt (exp_pos x))

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
lemma convex_on_pow_of_even {n : ℕ} (hn : even n) : convex_on 𝕜 set.univ (λ x : ℝ, x^n) :=
begin
  apply convex_on_univ_of_deriv2_nonneg differentiable_pow,
  { simp only [deriv_pow', differentiable.mul, differentiable_const, differentiable_pow] },
  { intro x,
    rcases nat.even.sub_even hn (nat.even_bit0 1) with ⟨k, hk⟩,
    rw [iter_deriv_pow, finset.prod_range_cast_nat_sub, hk, pow_mul'],
    exact mul_nonneg (nat.cast_nonneg _) (pow_two_nonneg _) }
end

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
lemma convex_on_pow (n : ℕ) : convex_on 𝕜 (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).continuous_on
    differentiable_on_pow,
  { simp only [deriv_pow'], exact differentiable_on_pow.const_mul _ },
  { intros x hx,
    rw [iter_deriv_pow, finset.prod_range_cast_nat_sub],
    exact mul_nonneg (nat.cast_nonneg _) (pow_nonneg (interior_subset hx) _) }
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
  rw [nat.succ_eq_add_one, mul_add, mul_one, bit0, ← add_assoc, finset.prod_range_succ,
    finset.prod_range_succ, mul_assoc],
  refine mul_nonneg ihn _, generalize : (1 + 1) * n = k,
  cases le_or_lt m k with hmk hmk,
  { have : m ≤ k + 1, from hmk.trans (lt_add_one ↑k).le,
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hmk) (sub_nonpos.2 this) },
  { exact mul_nonneg (sub_nonneg.2 hmk.le) (sub_nonneg.2 hmk) }
end

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
lemma convex_on_fpow (m : ℤ) : convex_on 𝕜 (Ioi 0) (λ x : ℝ, x^m) :=
begin
  have : ∀ n : ℤ, differentiable_on ℝ (λ x, x ^ n) (Ioi (0 : ℝ)),
    from λ n, differentiable_on_fpow _ _ (or.inl $ lt_irrefl _),
  apply convex_on_of_deriv2_nonneg (convex_Ioi 0);
    try { simp only [interior_Ioi, deriv_fpow'] },
  { exact (this _).continuous_on },
  { exact this _ },
  { exact (this _).const_mul _ },
  { intros x hx,
    simp only [iter_deriv_fpow, ← int.cast_coe_nat, ← int.cast_sub, ← int.cast_prod],
    refine mul_nonneg (int.cast_nonneg.2 _) (fpow_nonneg (le_of_lt hx) _),
    exact int_prod_range_nonneg _ _ (nat.even_bit0 1) }
end

lemma convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on 𝕜 (Ici 0) (λ x : ℝ, x^p) :=
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
    exact mul_nonneg (sub_nonneg_of_le hp) (rpow_nonneg_of_nonneg (le_of_lt hx) _) }
end

lemma concave_on_log_Ioi : concave_on 𝕜 (Ioi 0) log :=
begin
  have h₁ : Ioi 0 ⊆ ({0} : set ℝ)ᶜ,
  { intros x hx hx',
    rw [mem_singleton_iff] at hx',
    rw [hx'] at hx,
    exact lt_irrefl 0 hx },
  refine concave_on_open_of_deriv2_nonpos (convex_Ioi 0) is_open_Ioi _ _ _,
  { exact differentiable_on_log.mono h₁ },
  { refine ((times_cont_diff_on_log.deriv_of_open _ le_top).differentiable_on le_top).mono h₁,
    exact is_open_compl_singleton },
  { intros x hx,
    rw [function.iterate_succ, function.iterate_one],
    change (deriv (deriv log)) x ≤ 0,
    rw [deriv_log', deriv_inv],
    exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg x)) }
end

lemma concave_on_log_Iio : concave_on 𝕜 (Iio 0) log :=
begin
  have h₁ : Iio 0 ⊆ ({0} : set ℝ)ᶜ,
  { intros x hx hx',
    rw [mem_singleton_iff] at hx',
    rw [hx'] at hx,
    exact lt_irrefl 0 hx },
  refine concave_on_open_of_deriv2_nonpos (convex_Iio 0) is_open_Iio _ _ _,
  { exact differentiable_on_log.mono h₁ },
  { refine ((times_cont_diff_on_log.deriv_of_open _ le_top).differentiable_on le_top).mono h₁,
    exact is_open_compl_singleton },
  { intros x hx,
    rw [function.iterate_succ, function.iterate_one],
    change (deriv (deriv log)) x ≤ 0,
    rw [deriv_log', deriv_inv],
    exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg x)) }
end
