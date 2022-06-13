/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import number_theory.bernoulli_polynomials
import analysis.fourier

/-!
# Critical values of the Riemann zeta function

In this file we explicitly evaluate the Riemann zeta function `ζ(k) = ∑ (n : ℕ) 1 / n ^ k` for
positive even integers `k`. We follow the argument using Parseval's theorem for Fourier series
explained in the following reference:

## References
* [A. Ghorbanpour, M. Hatzel, *Parseval’s Identity and Values
    of Zeta Function at Even Integers*][ghorbanpour-hatzel]

## Main definitions and results

* `bernoulli_fun k x` : the function `(2 * π) ^ k * bernoulli k (x / (2 * π))`.
* `bernoulli_fourier_coeff_eq` : the `n`-th Fourier coefficient of `bernoulli_fun k` is
  `-k.factorial / (I * n) ^ k`.
* `bernoulli_norm` : the `L²` norm squared of `bernoulli k` on `[0, 2 * π]` is
  `(-1) ^ (k - 1) * (2 * π) ^ (2 * k + 1) * bernoulli (2 * k) / nat.choose (2 * k) k`. (This is a
  special case of a more general identity for the integral of
  `bernoulli_fun i x * bernoulli_fun j x` for any `1 ≤ i, j`.)
* `zeta_value`: the final formula,
  $$\zeta(2k) = \frac{(-1)^{(k - 1)} 2 ^ {2k - 1} π ^ {2k} B_{2 k}}{(2 k)!}.$$
-/

open_locale real complex_conjugate classical
open real complex measure_theory algebra submodule set interval_integral

noncomputable theory


section bernoulli_fun_props
/-! Simple properties of the function `Bₖ(x / (2 * π))`. -/

def bernoulli_fun0 (k : ℕ) (x : ℝ) : ℝ :=
(polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli k)).eval x

lemma has_deriv_at_bernoulli_fun0 (k : ℕ) (x : ℝ) :
  has_deriv_at (bernoulli_fun0 k) (k * bernoulli_fun0 (k - 1) x) x :=
begin
  have t := polynomial.has_deriv_at (polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli k)) x,
  rw [polynomial.derivative_map, polynomial.derivative_bernoulli k] at t,
  convert t,
  simp only [polynomial.map_mul, polynomial.map_nat_cast, polynomial.eval_mul,
    polynomial.eval_nat_cast, mul_eq_mul_left_iff, nat.cast_eq_zero],
  left, refl,
end

def bernoulli_fun (k : ℕ) (x : ℝ) : ℝ := (2 * π) ^ k * bernoulli_fun0 k (x / (2 * π))

lemma bernoulli_fun_zero : bernoulli_fun 0 = (λ x, 1 : ℝ → ℝ) :=
begin
  ext1 x,
  dsimp only [bernoulli_fun, bernoulli_fun0],
  rw polynomial.bernoulli_zero,
  simp,
end

lemma bernoulli_fun_eval_two_pi (k : ℕ) :
  bernoulli_fun k (2 * π) = bernoulli_fun k 0 + ite (k = 1) (2 * π) 0 :=
begin
  rw [bernoulli_fun, bernoulli_fun, bernoulli_fun0, bernoulli_fun0, div_self two_pi_pos.ne',
    zero_div, polynomial.eval_one_map, polynomial.eval_zero_map, polynomial.bernoulli_eval_one,
    polynomial.bernoulli_eval_zero],
  split_ifs,
  { rw [h, bernoulli_one, bernoulli'_one, pow_one],
    conv begin to_rhs, congr, skip, rw ←(mul_one (2 * π)), end,
    rw [← mul_add, algebra_map_eq_smul_one, algebra_map_eq_smul_one], norm_num },
  { rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero], }
end

lemma bernoulli_fun_eval_zero (k : ℕ): bernoulli_fun k 0 = (2 * π) ^ k * bernoulli k :=
begin
  dsimp only [bernoulli_fun, bernoulli_fun0],
  rw [zero_div, polynomial.eval_zero_map, polynomial.bernoulli_eval_zero],
  refl,
end

lemma has_deriv_at_bernoulli_fun (k : ℕ) (x : ℝ) : has_deriv_at (bernoulli_fun k)
  (k * bernoulli_fun (k - 1) x) x :=
begin
  have t : has_deriv_at (λ y:ℝ, y / (2 * π)) (1 / (2 * π)) x := (has_deriv_at_id x).div_const _,
  convert ((has_deriv_at_bernoulli_fun0 k _).comp _ t).const_mul ((2 * π) ^ k) using 1,
  rcases nat.eq_zero_or_pos k with hk|hk,
  { rw hk, simp,},
  rw bernoulli_fun, ring_nf, congr' 1,
  rw mul_comm, congr' 1, field_simp [two_pi_pos.ne'],
  rw [←pow_succ', nat.sub_add_cancel hk],
end

lemma continuous_bernoulli_fun (k : ℕ) : continuous (bernoulli_fun k) :=
begin
  rw continuous_iff_continuous_at, intro x,
  rcases (nat.eq_zero_or_pos k),
  { rw h, convert continuous_at_const,
    ext1, dsimp only [bernoulli_fun, bernoulli_fun0],
    rw [polynomial.bernoulli_zero, pow_zero, polynomial.map_one, polynomial.eval_one, mul_one], },
  { exact (has_deriv_at_bernoulli_fun k x).continuous_at },
end

lemma continuous_bernoulli_fun' (k : ℕ) : continuous (λ x, bernoulli_fun k x : ℝ → ℂ) :=
continuous_of_real.comp (continuous_bernoulli_fun k)

lemma integral_bernoulli_fun_eq_zero (k : ℕ) (hk : 1 ≤ k) :
  ∫ (x : ℝ) in 0..(2 * π), bernoulli_fun k x = 0 :=
begin
  have : ∀ x:ℝ, x ∈ interval 0 (2 * π) → has_deriv_at (λ y:ℝ, bernoulli_fun (k + 1) y / (k + 1))
    (bernoulli_fun k x) x,
  { intros x hx, convert (has_deriv_at_bernoulli_fun _ x).div_const (k + 1),
    simp only [nat.cast_add, nat.cast_one, nat.add_succ_sub_one, add_zero],
    rw [mul_comm, mul_div_assoc, div_self, mul_one],
    { rw [←nat.cast_one, ←nat.cast_add, nat.cast_ne_zero], exact nat.succ_ne_zero k },},
  rw integral_eq_sub_of_has_deriv_at this ((continuous_bernoulli_fun k).interval_integrable _ _),
  dsimp only,
  rw bernoulli_fun_eval_two_pi,
  split_ifs, { exfalso, linarith, }, { simp },
end

end bernoulli_fun_props

section bernoulli_fourier_coeffs
/-! Compute the Fourier coefficients of the Bernoulli functions. -/

def bernoulli_fourier_coeff (k : ℕ) (n : ℤ) : ℂ :=
  1 / (2 * π) * ∫ x in 0 .. 2 * π, exp (-n * I * x) * bernoulli_fun k x

lemma coefficient_recurrence (k : ℕ) (n : ℤ) (hn : n ≠ 0) : bernoulli_fourier_coeff k n =
  I / n * (- k * bernoulli_fourier_coeff (k - 1) n + ite (k = 1) 1 0) :=
begin
  rw [bernoulli_fourier_coeff],
  have d1 : ∀ (x:ℝ), has_deriv_at (λ x, bernoulli_fun k x : ℝ → ℂ) (k * bernoulli_fun (k - 1) x) x,
  { intro x, simpa using has_deriv_at.scomp x (of_real_clm.has_deriv_at)
      (has_deriv_at_bernoulli_fun k x) },
  have d2 : ∀ x:ℂ, has_deriv_at (λ y, I / n * exp (-n * I * y) : ℂ → ℂ) (exp (-n * I * x)) x,
  { intro x,
    suffices : has_deriv_at (λ y, exp (-n * I * y) : ℂ → ℂ) (exp (-n * I * x) * (-n * I)) x,
    { convert has_deriv_at.const_mul (I / n) this, ring_nf,
      rw [mul_inv_cancel (int.cast_ne_zero.mpr hn : (n : ℂ) ≠ 0), I_sq], ring, },
    refine has_deriv_at.comp x (complex.has_deriv_at_exp (-n * I * x)) _,
    simpa using (has_deriv_at_const x (-↑n * I)).mul (has_deriv_at_id x), },
  replace d2 : ∀ x:ℝ, has_deriv_at (λ y, I / n * exp (-n * I * y) : ℝ → ℂ)
    (exp (-n * I * x)) x,
  { intro x, simpa using has_deriv_at.comp x (d2 x) of_real_clm.has_deriv_at },
  have d := λ x (hx : x ∈ interval 0 (2 * π)), (d2 x).mul (d1 x),
  have int_ev := integral_eq_sub_of_has_deriv_at d _,
  swap, { apply continuous.interval_integrable,
    refine ((complex.continuous_exp.comp (continuous_const.mul continuous_of_real)).mul _).add
      ((continuous_const.mul (complex.continuous_exp.comp _)).mul
      (continuous_const.mul (continuous_bernoulli_fun' (k - 1)))),
    dsimp only, exact continuous_bernoulli_fun' k,
    exact continuous_const.mul continuous_of_real, },
  rw interval_integral.integral_add at int_ev,
  swap, { apply continuous.interval_integrable,
    refine (complex.continuous_exp.comp (continuous_const.mul continuous_of_real)).mul _,
    exact continuous_bernoulli_fun' k  },
  swap, { apply continuous.interval_integrable,
    refine (continuous_const.mul (complex.continuous_exp.comp _)).mul (continuous_const.mul _),
    exact continuous_const.mul continuous_of_real,
    exact continuous_bernoulli_fun' (k - 1) },
  rw eq_sub_of_add_eq int_ev, clear d d1 d2 int_ev,
  dsimp only,
  rw bernoulli_fun_eval_two_pi,
  have : (-↑n * I * ↑(2 * π)) = ↑(-n) * (2 * π * I) := by { simp, ring, },
  rw [this, exp_int_mul_two_pi_mul_I, of_real_zero, mul_zero, complex.exp_zero, of_real_add,
    add_comm, mul_add, add_sub_cancel, mul_one, mul_sub],
  have : 1 / (2 * ↑π) * ∫ (x : ℝ) in 0..2 * π, I / ↑n * exp (-↑n * I * ↑x)
    * (↑k * ↑(bernoulli_fun (k - 1) x)) = I / n * k * (bernoulli_fourier_coeff (k - 1) n),
  { dsimp only [bernoulli_fourier_coeff],
    rw [←integral_const_mul, ←integral_const_mul, ←integral_const_mul],
    apply integral_congr, intros x hx, dsimp only,
    ring, },
  rw this, split_ifs,
  { rw of_real_mul, simp only [of_real_bit0, of_real_one, neg_mul],
    field_simp [of_real_ne_zero.mpr pi_pos.ne'], ring,  },
  { simp only [of_real_zero, mul_zero, zero_sub, neg_mul, add_zero, mul_neg, neg_inj], ring },
end

lemma bernoulli_fourier_coeff_zero (n : ℤ) (hn : n ≠ 0): bernoulli_fourier_coeff 0 n = 0 :=
begin
  dsimp only [bernoulli_fourier_coeff, bernoulli_fun, bernoulli_fun0],
  simp_rw polynomial.bernoulli_zero,
  simp only [one_div, mul_inv_rev, pow_zero, polynomial.map_one, polynomial.eval_one,
    mul_one, of_real_one, mul_eq_zero, inv_eq_zero, of_real_eq_zero, bit0_eq_zero, one_ne_zero,
    or_false, pi_ne_zero, false_or],
  rw integral_exp_mul_complex (mul_ne_zero (neg_ne_zero.mpr (int.cast_ne_zero.mpr hn)) I_ne_zero),
  have : -↑n * I * ↑(2 * π) = ↑(-n) * (2 * π * I),
  { rw [int.cast_neg, of_real_mul, of_real_bit0, of_real_one], ring, },
  rw [this, exp_int_mul_two_pi_mul_I, of_real_zero, mul_zero, complex.exp_zero, sub_self, zero_div]
end

lemma bernoulli_fourier_coeff_eq (k : ℕ) (hk : 1 ≤ k) (n : ℤ) :
  bernoulli_fourier_coeff k n = -k.factorial / (I * n) ^ k :=
begin
  rcases eq_or_ne n 0 with hn|hn,
  { -- first deal with the n = 0 case
    rw hn, dsimp only [bernoulli_fourier_coeff],
    simp only [int.cast_zero, neg_zero', zero_mul, complex.exp_zero, one_mul, mul_zero],
    rw zero_pow (by linarith : 0 < k),
    simp only [div_zero, mul_eq_zero, inv_eq_zero, of_real_eq_zero, bit0_eq_zero,
      one_ne_zero, or_false], right,
    -- this step is more awkward than it should be since there is no `interval_integral.of_real`
    rw [interval_integral_eq_integral_interval_oc, integral_of_real],
    have := integral_bernoulli_fun_eq_zero k hk,
    rw interval_integral_eq_integral_interval_oc at this,
    simp only [two_pi_pos.le, if_true, id.smul_eq_mul, one_mul] at this,
    rw this, simp, },
  induction k with k h, -- no tidy way to induct starting at 1?
  { exfalso, linarith, },
  { rw coefficient_recurrence k.succ n hn,
    rcases eq_or_ne k 0 with h'|h',
    { rw h',
      simp only [nat.cast_one, tsub_self, neg_mul, one_mul, eq_self_iff_true, if_true,
      nat.factorial_one, pow_one, inv_I, mul_neg],
      rw bernoulli_fourier_coeff_zero _ hn,
      field_simp [int.cast_ne_zero.mpr hn, I_ne_zero],
      rw [←mul_assoc, I_mul_I, neg_one_mul], },
    rw [nat.succ_sub_one, h (nat.pos_of_ne_zero h')],
    split_ifs,
    { exfalso, contrapose! h', rw nat.succ_eq_one_add at h_1, linarith,  },
    { rw [nat.factorial_succ, nat.succ_eq_add_one, add_zero, nat.cast_mul, pow_add, pow_one],
      field_simp [int.cast_ne_zero.mpr hn, I_ne_zero],
      ring_nf, rw I_sq, ring, } }
end

end bernoulli_fourier_coeffs

section bernoulli_L2_norm
/-! We evaluate the integral of `Bᵢ(x) Bⱼ(x)`by using repeated integration by parts. As a special
case we deduce the `L²` norm of `Bₖ`.  -/

lemma bernoulli_prod_recurrence (i : ℕ) (hi : i ≠ 0) (j : ℕ) :
  ∫ x:ℝ in 0..(2 * π), bernoulli_fun i x * bernoulli_fun j x =
  ite (j = 1) (2 * π * bernoulli_fun (i + 1) 0 / (i + 1)) 0
  - j / (i + 1) * ∫ x:ℝ in 0..(2 * π), bernoulli_fun (i+1) x * bernoulli_fun (j-1) x :=
begin
  have t : ∀ x:ℝ, x ∈ interval 0 (2 * π) → has_deriv_at (λ y, bernoulli_fun (i+1) y / (i + 1) )
    (bernoulli_fun i x) x,
  { intros x hx, have t := (has_deriv_at_bernoulli_fun (i + 1) x).div_const (i + 1),
    convert t,
    rw [mul_comm, nat.cast_add, nat.cast_one, mul_div_cancel, nat.add_sub_cancel],
    rw [←nat.cast_one, ←nat.cast_add, nat.cast_ne_zero], exact i.add_one_ne_zero, },
  replace t := integral_mul_deriv_eq_deriv_mul (λ x hx, @has_deriv_at_bernoulli_fun j x) t _ _,
  swap, { exact (continuous_const.mul $ continuous_bernoulli_fun $ j - 1).interval_integrable _ _ },
  swap, { exact (continuous_bernoulli_fun _).interval_integrable _ _ },
  have : (λ x:ℝ, bernoulli_fun j x * bernoulli_fun i x)
    = (λ x:ℝ, bernoulli_fun i x * bernoulli_fun j x) := by { ext1 x, ring },
  dsimp at t, rw this at t,
  rw [t, bernoulli_fun_eval_two_pi, bernoulli_fun_eval_two_pi],
  simp only [add_left_eq_self],
  split_ifs,
  { -- j = 1 case
    rw [←integral_const_mul, add_zero, add_mul, add_sub_cancel', h],
    congr' 1, { ring }, congr' 1, { ext1 x, ring, } },
  { -- j ≠ 1 case
    rw [←integral_const_mul, add_zero, add_zero, sub_self, zero_sub, zero_sub, neg_inj],
    apply integral_congr,
    intros x hx, dsimp only, ring },
end

lemma bernoulli_prod (m : ℕ) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ m) :
  ∫ x:ℝ in 0..(2 * π), bernoulli_fun (m - j) x * bernoulli_fun j x =
  (-1) ^ (j - 1) * (2 * π) ^ (m + 1) * bernoulli m / nat.choose m j :=
begin
  -- This proof is a bit painful. Firstly, it is induction on `j` but with a hypothesis `1 ≤ j`;
  -- so the "base case" `j = 0` is a trivial exfalso, and the actual base case `j = 1` appears later
  -- as an `rcases` construct. Secondly, there are lots of inequalities with `nat`s, where
  -- subtraction behaves in counterintuitive ways.
  induction j with j hj,
  { exfalso, linarith },
  { simp_rw nat.succ_eq_add_one at *,
    rw bernoulli_prod_recurrence (m - (j + 1)) _ (j + 1),
    swap, { contrapose! hj2, simp only [tsub_eq_zero_iff_le] at hj2, linarith },
    have w : m - (j + 1) + 1 = m - j,
    { rw [←nat.sub_sub, nat.sub_add_cancel],
      replace hj2 := nat.le_of_succ_le hj2,
      rwa [add_comm, nat.add_le_to_le_sub] at hj2,
      linarith,},
    simp_rw [w, (by ring: j + 1 - 1 = j)],
    rcases nat.eq_zero_or_pos j,
    { -- j=0 case
      simp_rw h,
      simp only [zero_add, eq_self_iff_true, tsub_zero, if_true, nat.cast_one, pow_zero, one_mul,
        nat.choose_one_right],
      simp_rw [bernoulli_fun_zero, mul_one],
      rw [integral_bernoulli_fun_eq_zero, mul_zero, bernoulli_fun_eval_zero],
      swap, { rw h at hj2, linarith },
      have : (((m - 1) : ℕ): ℝ) + 1 = m := by { rw nat.cast_sub, simp, linarith },
      rw [this, pow_add],
      ring },
    { rw hj (by linarith) (by linarith),
      split_ifs, { exfalso, linarith },
      rw [nat.cast_sub (by linarith : j + 1 ≤ m), nat.cast_add, nat.cast_one, zero_sub],
      have : (-1 : ℝ) ^ j = - (-1) ^ (j - 1),
      { have : j = (j - 1) + 1 := by { rw nat.sub_add_cancel, linarith,},
        conv_lhs { rw this }, rw pow_add, simp },
      rw [this, sub_add, add_sub_cancel],
      -- prepare `≠ 0` statements for `field_simp`
      have a : ((m.choose j) : ℝ) ≠ 0,
      { rw [nat.cast_ne_zero, ne.def, nat.choose_eq_zero_iff], linarith, },
      have b : ((m.choose (j + 1)) : ℝ) ≠ 0,
      { rw [nat.cast_ne_zero, ne.def, nat.choose_eq_zero_iff], linarith, },
      have c : (↑m - ↑j : ℝ) ≠ 0,
      { rw [sub_ne_zero, ne.def, nat.cast_inj], linarith },
      field_simp,
      have : ((j:ℝ) + 1) * ((-1) ^ (j - 1) * (2 * π) ^ (m + 1) * (bernoulli m))
        * (m.choose (j + 1)) = ((j:ℝ) + 1) * ↑(m.choose (j + 1)) * (-1) ^ (j - 1)
        * (2 * π) ^ (m + 1) * (bernoulli m) := by ring, rw this,
      have : (-1) ^ (j - 1) * (2 * π) ^ (m + 1) * (bernoulli m) * ((↑m - ↑j) * ↑(m.choose j)) =
        ((m:ℝ) - ↑j) * ↑(m.choose j) * (-1) ^ (j - 1) * (2 * π) ^ (m + 1) * ↑(bernoulli m) :=
      by ring, rw this,
      congr' 3,
      rw [←nat.cast_one, ←nat.cast_add, ←nat.cast_mul, ←nat.cast_sub, ←nat.cast_mul, nat.cast_inj],
      conv_lhs { rw mul_comm }, conv_rhs { rw mul_comm },
      rw nat.choose_succ_right_eq,
      linarith } },
end

lemma bernoulli_norm (k : ℕ) (hk : 1 ≤ k) : ∫ x:ℝ in 0..(2 * π), (bernoulli_fun k x) ^ 2 =
  (-1) ^ (k - 1) * (2 * π) ^ (2 * k + 1) * bernoulli (2 * k) / nat.choose (2 * k) k :=
begin
  convert bernoulli_prod (2 * k) k hk _,
  { ext1 x, rw sq, congr, rw [two_mul, nat.add_sub_cancel], },
  { rw two_mul, apply nat.add_le_add_left hk },
end

end bernoulli_L2_norm

section main_proof

lemma zeta_ℤ (k : ℕ) (hk : 1 ≤ k) : has_sum (λ (n : ℤ), 1 / (n : ℝ) ^ (2 * k))
  ((-1) ^ (k - 1) * 2 ^ (2 * k) * π ^ (2 * k) * bernoulli (2 * k) / ((2 * k).factorial)) :=
begin
  have t := fourier_line.parseval_line (λ x, bernoulli_fun k x) _,
  swap, { rw mem_ℒp_two_iff_integrable_sq_norm,
    exact ((continuous_norm.comp (continuous_bernoulli_fun' k)).pow 2).integrable_on_Ioc,
    exact (continuous_bernoulli_fun' k).ae_strongly_measurable },
  have s := bernoulli_fourier_coeff_eq k hk,
  dsimp only [bernoulli_fourier_coeff] at s t,
  simp_rw [s, complex.norm_eq_abs, abs_of_real, _root_.sq_abs] at t,
  have : 1 / (2 * π) * ∫ (x : ℝ) in 0..2 * π, bernoulli_fun k x ^ 2 =
    (-1) ^ (k - 1) * (2 * π) ^ (2 * k) * bernoulli (2 * k) / nat.choose (2 * k) k,
  { rw [bernoulli_norm k hk, pow_add, pow_one, mul_div],
    congr' 1, field_simp [two_pi_pos.ne'], ring, },
  rw this at t,
  simp_rw [complex.abs_div, complex.abs_neg, mul_pow, complex.abs_mul,
    complex.abs_pow, abs_I, one_pow, one_mul, div_pow] at t,
  have : ∀ (n : ℕ), complex.abs ( (n : ℂ) ) = (n : ℝ),
  { intro n, have : (n : ℂ) = ((n : ℝ) : ℂ) := by simp,
    rw [this, complex.abs_of_real, nat.abs_cast],  },
  simp_rw [this] at t,
  have : ∀ (n : ℤ), complex.abs ( (n : ℂ) ) = |(n : ℝ)|,
  { intro n, have : (n : ℂ) = ((n : ℝ) : ℂ) := by simp,
    rw [this, complex.abs_of_real],  },
  simp_rw [this,  ←pow_mul, mul_comm k 2, pow_mul, _root_.sq_abs, ←pow_mul] at t,
  replace t := has_sum.div_const t ((k.factorial) ^ 2),
  have : (λ (n : ℤ), ↑(k.factorial) ^ 2 / (n : ℝ) ^ (2 * k) / ↑(k.factorial) ^ 2) =
    (λ (n : ℤ), 1 / (n : ℝ) ^ (2 * k)),
  { ext1 n, rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm, ←mul_assoc, inv_mul_cancel],
    field_simp, rw [ne.def, sq_eq_zero_iff, ←ne.def, nat.cast_ne_zero],
    exact nat.factorial_ne_zero k },
  rw [this, div_div, sq] at t,
  have : (((2 * k).choose k) : ℝ) * (↑(k.factorial) * ↑(k.factorial)) = ( (2 * k).factorial ),
  { rw [←nat.cast_mul, ←nat.cast_mul, ←mul_assoc], congr' 1,
    convert nat.choose_mul_factorial_mul_factorial (by linarith : k ≤ 2 * k),
    rw [two_mul, nat.add_sub_cancel], },
  rwa [this, ←mul_assoc] at t

end

lemma zeta_value (k : ℕ) (hk : 1 ≤ k) : has_sum (λ n:ℕ, 1 / ((n + 1) : ℝ) ^ (2 * k))
  ((-1) ^ (k - 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / ((2 * k).factorial)) :=
begin
  have := (zeta_ℤ k hk).sum_ℕ_of_sum_ℤ,
  simp only [int.cast_add, int.cast_coe_nat, int.cast_one, int.cast_sub, int.cast_neg,
    int.cast_zero] at this,
  have aux : ∀ (n:ℕ), (-(n:ℝ) - 1) ^ (2 * k) = ((n:ℝ) + 1) ^ (2 * k),
  { intro n, rw [pow_mul, pow_mul, neg_sub_left, neg_sq, add_comm],},
  simp_rw [aux, ←mul_two] at this,
  convert (this.div_const 2) using 1,
  { ext1, simp, },
  { field_simp,
    have : (-1) ^ (k - 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * ↑(bernoulli (2 * k)) * 2 =
    (-1) ^ (k - 1) * (2 ^ (2 * k - 1) * 2 ^ 1) * π ^ (2 * k) * ↑(bernoulli (2 * k)),
    { rw pow_one, ring, },
    rw [this, ←pow_add, nat.sub_add_cancel (by linarith : 1 ≤ 2 * k),
      zero_pow (by linarith : 0 < 2 * k), div_zero, sub_zero], },
end

end main_proof

section examples

lemma zeta_two : has_sum (λ n:ℕ, 1 / ((n + 1) : ℝ) ^ 2) (π ^ 2 / 6) :=
begin
  convert zeta_value 1 (le_refl _) using 1, norm_num,
  rw [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_two],
  norm_num, field_simp, ring, dec_trivial,
end

lemma zeta_four : has_sum (λ n:ℕ, 1 / ((n + 1) : ℝ) ^ 4) (π ^ 4 / 90) :=
begin
  convert zeta_value 2 one_le_two using 1, norm_num,
  rw [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four],
  norm_num, field_simp, ring, dec_trivial,
end

end examples
