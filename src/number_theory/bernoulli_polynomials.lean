/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, David Loeffler
-/
import data.polynomial.algebra_map
import data.polynomial.derivative
import data.nat.choose.cast
import number_theory.bernoulli
import analysis.special_functions.integrals
import measure_theory.integral.interval_integral
import analysis.fourier.add_circle

/-!
# Bernoulli polynomials

The [Bernoulli polynomials](https://en.wikipedia.org/wiki/Bernoulli_polynomials)
are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n$-th Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n \choose k} (-1)^k  B_k  X^{n - k} $$
where $B_k$ is the $k$-th Bernoulli number. The Bernoulli polynomials are generating functions,
$$ \frac{t  e^{tX} }{ e^t - 1} = ∑_{n = 0}^{\infty} B_n(X)  \frac{t^n}{n!} $$

## Implementation detail

Bernoulli polynomials are defined using `bernoulli`, the Bernoulli numbers.

## Main theorems

- `sum_bernoulli`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to `n` is `(n + 1) * X^n`.
- `polynomial.bernoulli_generating_function`: The Bernoulli polynomials act as generating functions
  for the exponential.

## TODO

- `bernoulli_eval_one_neg` : $$ B_n(1 - x) = (-1)^n B_n(x) $$

-/

noncomputable theory
open_locale big_operators
open_locale nat polynomial

open nat finset

namespace polynomial

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers. -/
def bernoulli (n : ℕ) : ℚ[X] :=
  ∑ i in range (n + 1), polynomial.monomial (n - i) ((_root_.bernoulli i) * (choose n i))

lemma bernoulli_def (n : ℕ) : bernoulli n =
  ∑ i in range (n + 1), polynomial.monomial i ((_root_.bernoulli (n - i)) * (choose n i)) :=
begin
  rw [←sum_range_reflect, add_succ_sub_one, add_zero, bernoulli],
  apply sum_congr rfl,
  rintros x hx,
  rw mem_range_succ_iff at hx, rw [choose_symm hx, tsub_tsub_cancel_of_le hx],
end

/-
### examples
-/

section examples

@[simp] lemma bernoulli_zero : bernoulli 0 = 1 :=
by simp [bernoulli]

@[simp] lemma bernoulli_eval_zero (n : ℕ) : (bernoulli n).eval 0 = _root_.bernoulli n :=
begin
 rw [bernoulli, eval_finset_sum, sum_range_succ],
  have : ∑ (x : ℕ) in range n, _root_.bernoulli x * (n.choose x) * 0 ^ (n - x) = 0,
  { apply sum_eq_zero (λ x hx, _),
    have h : 0 < n - x := tsub_pos_of_lt (mem_range.1 hx),
    simp [h] },
  simp [this],
end

@[simp] lemma bernoulli_eval_one (n : ℕ) : (bernoulli n).eval 1 = _root_.bernoulli' n :=
begin
  simp only [bernoulli, eval_finset_sum],
  simp only [←succ_eq_add_one, sum_range_succ, mul_one, cast_one, choose_self,
    (_root_.bernoulli _).mul_comm, sum_bernoulli, one_pow, mul_one, eval_C, eval_monomial],
  by_cases h : n = 1,
  { norm_num [h], },
  { simp [h],
    exact bernoulli_eq_bernoulli'_of_ne_one h, }
end

end examples

lemma derivative_bernoulli_add_one (k : ℕ) :
  (bernoulli (k + 1)).derivative = (k + 1) * bernoulli k :=
begin
  simp_rw [bernoulli, derivative_sum, derivative_monomial, nat.sub_sub, nat.add_sub_add_right],
  -- LHS sum has an extra term, but the coefficient is zero:
  rw [range_add_one, sum_insert not_mem_range_self, tsub_self, cast_zero, mul_zero, map_zero,
    zero_add, mul_sum],
  -- the rest of the sum is termwise equal:
  refine sum_congr (by refl) (λ m hm, _),
  conv_rhs { rw [←nat.cast_one, ←nat.cast_add, ←C_eq_nat_cast, C_mul_monomial, mul_comm], },
  rw [mul_assoc, mul_assoc, ←nat.cast_mul, ←nat.cast_mul],
  congr' 3,
  rw [(choose_mul_succ_eq k m).symm, mul_comm],
end

lemma derivative_bernoulli (k : ℕ) : (bernoulli k).derivative = k * bernoulli (k - 1) :=
begin
  cases k,
  { rw [nat.cast_zero, zero_mul, bernoulli_zero, derivative_one], },
  { exact_mod_cast derivative_bernoulli_add_one k, }
end

@[simp] theorem sum_bernoulli (n : ℕ) :
  ∑ k in range (n + 1), ((n + 1).choose k : ℚ) • bernoulli k = monomial n (n + 1 : ℚ) :=
begin
 simp_rw [bernoulli_def, finset.smul_sum, finset.range_eq_Ico, ←finset.sum_Ico_Ico_comm,
    finset.sum_Ico_eq_sum_range],
  simp only [add_tsub_cancel_left, tsub_zero, zero_add, linear_map.map_add],
  simp_rw [smul_monomial, mul_comm (_root_.bernoulli _) _, smul_eq_mul, ←mul_assoc],
  conv_lhs { apply_congr, skip, conv
    { apply_congr, skip,
      rw [← nat.cast_mul, choose_mul ((le_tsub_iff_left $ mem_range_le H).1
        $ mem_range_le H_1) (le.intro rfl), nat.cast_mul, add_comm x x_1, add_tsub_cancel_right,
        mul_assoc, mul_comm, ←smul_eq_mul, ←smul_monomial] },
    rw [←sum_smul], },
  rw [sum_range_succ_comm],
  simp only [add_right_eq_self, mul_one, cast_one, cast_add, add_tsub_cancel_left,
    choose_succ_self_right, one_smul, _root_.bernoulli_zero, sum_singleton, zero_add,
    linear_map.map_add, range_one],
  apply sum_eq_zero (λ x hx, _),
  have f : ∀ x ∈ range n, ¬ n + 1 - x = 1,
  { rintros x H, rw [mem_range] at H,
    rw [eq_comm],
    exact ne_of_lt (nat.lt_of_lt_of_le one_lt_two (le_tsub_of_add_le_left (succ_le_succ H))) },
  rw [sum_bernoulli],
  have g : (ite (n + 1 - x = 1) (1 : ℚ) 0) = 0,
  { simp only [ite_eq_right_iff, one_ne_zero],
    intro h₁,
    exact (f x hx) h₁, },
  rw [g, zero_smul],
end

/-- Another version of `polynomial.sum_bernoulli`. -/
lemma bernoulli_eq_sub_sum (n : ℕ) : (n.succ : ℚ) • bernoulli n = monomial n (n.succ : ℚ) -
  ∑ k in finset.range n, ((n + 1).choose k : ℚ) • bernoulli k :=
by rw [nat.cast_succ, ← sum_bernoulli n, sum_range_succ, add_sub_cancel',
  choose_succ_self_right, nat.cast_succ]

/-- Another version of `bernoulli.sum_range_pow`. -/
lemma sum_range_pow_eq_bernoulli_sub (n p : ℕ) :
  (p + 1 : ℚ) * ∑ k in range n, (k : ℚ) ^ p = (bernoulli p.succ).eval n -
  (_root_.bernoulli p.succ) :=
begin
  rw [sum_range_pow, bernoulli_def, eval_finset_sum, ←sum_div, mul_div_cancel' _ _],
  { simp_rw [eval_monomial],
    symmetry,
    rw [←sum_flip _, sum_range_succ],
    simp only [tsub_self, tsub_zero, choose_zero_right, cast_one, mul_one, pow_zero,
      add_tsub_cancel_right],
    apply sum_congr rfl (λ x hx, _),
    apply congr_arg2 _ (congr_arg2 _ _ _) rfl,
    { rw nat.sub_sub_self (mem_range_le hx), },
    { rw ←choose_symm (mem_range_le hx), }, },
  { norm_cast, apply succ_ne_zero _, },
end

/-- Rearrangement of `polynomial.sum_range_pow_eq_bernoulli_sub`. -/
lemma bernoulli_succ_eval (n p : ℕ) : (bernoulli p.succ).eval n =
  _root_.bernoulli (p.succ) + (p + 1 : ℚ) * ∑ k in range n, (k : ℚ) ^ p :=
by { apply eq_add_of_sub_eq', rw sum_range_pow_eq_bernoulli_sub, }

lemma bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
  (bernoulli n).eval (1 + x) = (bernoulli n).eval x + n * x^(n - 1) :=
begin
  apply nat.strong_induction_on n (λ d hd, _),
  have nz : ((d.succ : ℕ): ℚ) ≠ 0,
  { norm_cast, exact d.succ_ne_zero, },
  apply (mul_right_inj' nz).1,
  rw [← smul_eq_mul, ←eval_smul, bernoulli_eq_sub_sum, mul_add, ←smul_eq_mul,
    ←eval_smul, bernoulli_eq_sub_sum, eval_sub, eval_finset_sum],
  conv_lhs { congr, skip, apply_congr, skip, rw [eval_smul, hd x_1 (mem_range.1 H)], },
  rw [eval_sub, eval_finset_sum],
  simp_rw [eval_smul, smul_add],
  rw [sum_add_distrib, sub_add, sub_eq_sub_iff_sub_eq_sub, _root_.add_sub_sub_cancel],
  conv_rhs { congr, skip, congr, rw [succ_eq_add_one, ←choose_succ_self_right d], },
  rw [nat.cast_succ, ← smul_eq_mul, ←sum_range_succ _ d, eval_monomial_one_add_sub],
  simp_rw [smul_eq_mul],
end

open power_series
variables {A : Type*} [comm_ring A] [algebra ℚ A]

-- TODO: define exponential generating functions, and use them here
-- This name should probably be updated afterwards

/-- The theorem that $(e^X - 1) * ∑ Bₙ(t)* X^n/n! = Xe^{tX}$ -/
theorem bernoulli_generating_function (t : A) :
  mk (λ n, aeval t ((1 / n! : ℚ) • bernoulli n)) * (exp A - 1) =
    power_series.X * rescale t (exp A) :=
begin
  -- check equality of power series by checking coefficients of X^n
  ext n,
  -- n = 0 case solved by `simp`
  cases n, { simp },
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul, coeff_rescale, coeff_exp, power_series.coeff_mul,
    nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ],
  -- last term is zero so kill with `add_zero`
  simp only [ring_hom.map_sub, tsub_self, constant_coeff_one, constant_coeff_exp,
    coeff_zero_eq_constant_coeff, mul_zero, sub_self, add_zero],
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  have hnp1 : is_unit ((n+1)! : ℚ) := is_unit.mk0 _ (by exact_mod_cast factorial_ne_zero (n+1)),
  rw ←(hnp1.map (algebra_map ℚ A)).mul_right_inj,
  -- do trivial rearrangements to make RHS (n+1)*t^n
  rw [mul_left_comm, ←ring_hom.map_mul],
  change _ = t^n * algebra_map ℚ A (((n+1)*n! : ℕ)*(1/n!)),
  rw [cast_mul, mul_assoc, mul_one_div_cancel
    (show (n! : ℚ) ≠ 0, from cast_ne_zero.2 (factorial_ne_zero n)), mul_one, mul_comm (t^n),
    ← aeval_monomial, cast_add, cast_one],
  -- But this is the RHS of `sum_bernoulli_poly`
  rw [← sum_bernoulli, finset.mul_sum, alg_hom.map_sum],
  -- and now we have to prove a sum is a sum, but all the terms are equal.
  apply finset.sum_congr rfl,
  -- The rest is just trivialities, hampered by the fact that we're coercing
  -- factorials and binomial coefficients between ℕ and ℚ and A.
  intros i hi,
  -- deal with coefficients of e^X-1
  simp only [nat.cast_choose ℚ (mem_range_le hi), coeff_mk,
    if_neg (mem_range_sub_ne_zero hi), one_div, alg_hom.map_smul, power_series.coeff_one,
    coeff_exp, sub_zero, linear_map.map_sub, algebra.smul_mul_assoc, algebra.smul_def,
    mul_right_comm _ ((aeval t) _), ←mul_assoc, ← ring_hom.map_mul, succ_eq_add_one,
    ← polynomial.C_eq_algebra_map, polynomial.aeval_mul, polynomial.aeval_C],
  -- finally cancel the Bernoulli polynomial and the algebra_map
  congr',
  apply congr_arg,
  rw [mul_assoc, div_eq_mul_inv, ← mul_inv],
end

end polynomial

/-
## Fourier coefficients of the Bernoulli polynomials
-/
open_locale real interval
open complex measure_theory set interval_integral

section fourier_lemmas
/-! General lemmas about Fourier theory -/
parameter {T : ℝ}

lemma has_deriv_at_fourier (n : ℤ) (x : ℝ) : has_deriv_at (λ y:ℝ, @fourier T n y)
  (2 * π * I * n / T * @fourier T n x) x :=
begin
  simp_rw [fourier_coe_apply],
  refine (_ : has_deriv_at (λ y, exp (2 * π * I * n * y / T)) _ _).comp_of_real,
  rw (λ α β, by ring : ∀ (α β : ℂ), α * exp β = exp β * α),
  refine (has_deriv_at_exp _).comp x _,
  convert has_deriv_at_mul_const (2 * ↑π * I * ↑n / T),
  ext1 y, ring,
end
lemma has_deriv_at_fourier_neg (n : ℤ) (x : ℝ) : has_deriv_at (λ y:ℝ, @fourier T (-n) y)
  (-2 * π * I * n / T * @fourier T (-n) x) x :=
by simpa using has_deriv_at_fourier (-n) x

lemma has_antideriv_at_fourier_neg (hT : fact (0 < T)) {n : ℤ} (hn : n ≠ 0) (x : ℝ) : has_deriv_at
  (λ (y : ℝ), ↑T / (-2 * ↑π * I * ↑n) * @fourier T (-n) y) (@fourier T (-n) x) x :=
begin
  convert (has_deriv_at_fourier_neg n x).div_const (-2 * π * I * n / T),
  { ext1 y, rw div_div_eq_mul_div, ring, },
  { rw mul_div_cancel_left,
    simp only [ne.def, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, bit0_eq_zero, one_ne_zero,
      of_real_eq_zero, false_or, int.cast_eq_zero, not_or_distrib],
    exact ⟨⟨⟨real.pi_ne_zero, I_ne_zero⟩, hn⟩, hT.out.ne'⟩ },
end

/-- Express Fourier coefficients of `f` in terms of those of its derivative `f'`. -/
lemma fourier_coeff_eq_of_has_deriv_at {hT : fact (0 < T)}  {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
  (hf : ∀ x, x ∈ [0, T] → has_deriv_at f (f' x) x) (hf' : interval_integrable f' volume 0 T)  :
∫ x in 0..T, @fourier T (-n) x * f x =
  T / (-2 * π * I * n) * (f T - f 0 - ∫ x in 0..T, @fourier T (-n) x * f' x) :=
begin
  simp_rw [(by {intros, ring} : ∀ α β n, @fourier T (-n) α * β = β * @fourier T (-n) α)],
  rw integral_mul_deriv_eq_deriv_mul hf (λ x hx, has_antideriv_at_fourier_neg hT hn x) hf'
    (((map_continuous (fourier (-n))).comp (add_circle.continuous_mk' T)
    ).interval_integrable _ _),
  dsimp only,
  have : @fourier T (-n) T = 1,
  { rw fourier_coe_apply,
    convert exp_int_mul_two_pi_mul_I (-n) using 2,
    rw mul_div_cancel _ (of_real_ne_zero.mpr hT.out.ne'),
    norm_cast, ring  },
  rw [this, @fourier_coe_apply T _ _, of_real_zero, mul_zero, mul_one,
    zero_div, exp_zero, mul_one, ←sub_mul],
  have : ∀ (u v w : ℂ), u * (T / v * w) = T / v * (u * w) := by {intros, ring},
  conv_lhs { congr, skip, congr, funext, rw this, },
  rw [integral_const_mul, mul_comm (f T - f 0) _, ←mul_sub],
end

end fourier_lemmas

local notation `e` := @fourier 1

section bernoulli_fun_props
/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/

/-- The function `x ↦ Bₖ(x) : ℝ → ℝ`. -/
def bernoulli_fun (k : ℕ) (x : ℝ) : ℝ :=
(polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli k)).eval x

local notation `B` := bernoulli_fun

lemma bernoulli_fun_eval_zero (k : ℕ): B k 0 = bernoulli k :=
by rw [bernoulli_fun, polynomial.eval_zero_map, polynomial.bernoulli_eval_zero, eq_rat_cast]

lemma bernoulli_fun_endpoints_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) : B k 0 = B k 1 :=
by rw [bernoulli_fun_eval_zero, bernoulli_fun, polynomial.eval_one_map,
  polynomial.bernoulli_eval_one, bernoulli_eq_bernoulli'_of_ne_one hk, eq_rat_cast]

lemma bernoulli_fun_eval_one (k : ℕ) : B k 1 = B k 0 + ite (k = 1) 1 0 :=
begin
  rw [bernoulli_fun, bernoulli_fun_eval_zero, polynomial.eval_one_map,
    polynomial.bernoulli_eval_one],
  split_ifs,
  { rw [h, bernoulli_one, bernoulli'_one, eq_rat_cast, rat.cast_div, rat.cast_div, rat.cast_neg,
    rat.cast_bit0, rat.cast_one], -- somehow norm_cast doesn't handle this?
    ring },
  { rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero, eq_rat_cast], }
end

lemma has_deriv_at_bernoulli_fun (k : ℕ) (x : ℝ) : has_deriv_at (B k)
  (k * bernoulli_fun (k - 1) x) x :=
begin
  convert ((polynomial.bernoulli k).map $ algebra_map ℚ ℝ).has_deriv_at x using 1,
  simp only [bernoulli_fun, polynomial.derivative_map, polynomial.derivative_bernoulli k,
    polynomial.map_mul, polynomial.map_nat_cast, polynomial.eval_mul, polynomial.eval_nat_cast],
end

lemma antideriv_bernoulli_fun (k : ℕ) (x : ℝ) :
  has_deriv_at (λ x, (B (k + 1) x) / (k + 1)) (B k x) x :=
begin
  convert (has_deriv_at_bernoulli_fun (k + 1) x).div_const _,
  field_simp [nat.cast_add_one_ne_zero k],
  ring,
end

lemma integral_bernoulli_fun_eq_zero (k : ℕ) (hk : 1 ≤ k) :
  ∫ (x : ℝ) in 0..1, B k x = 0 :=
begin
  rw integral_eq_sub_of_has_deriv_at (λ x hx, antideriv_bernoulli_fun k x)
    ((polynomial.continuous _).interval_integrable _ _),
  dsimp only,
  rw bernoulli_fun_eval_one,
  split_ifs,
  { exfalso, linarith, }, { simp },
end

end bernoulli_fun_props

/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/
section bernoulli_fourier_coeffs

/-- The `n`-th Fourier coefficient of the `k`-th Bernoulli function. -/
def bernoulli_fourier_coeff (k : ℕ) (n : ℤ) : ℂ :=
  ∫ x in 0..1, e (-n) x * bernoulli_fun k x

/-- Recurrence relation (in `k`) for the `n`-th Fourier coefficient of `Bₖ`. -/
lemma coefficient_recurrence (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
∫ x in 0..1, e (-n) x * bernoulli_fun k x = 1 / ((-2) * ↑π * I * ↑n) *
  (ite (k = 1) 1 0 - k * ∫ x in 0..1, e (-n) x * bernoulli_fun (k - 1) x) :=
begin
  rw [fourier_coeff_eq_of_has_deriv_at hn (λ x hx, (has_deriv_at_bernoulli_fun k x).of_real_comp)
    ((continuous_of_real.comp $ continuous_const.mul
      $ polynomial.continuous _).interval_integrable _ _)],
  dsimp only,
  rw [←of_real_sub, bernoulli_fun_eval_one, add_sub_cancel'],
  congr' 2,
  { split_ifs, all_goals { simp only [of_real_one, of_real_zero]} },
  { simp_rw [of_real_mul, (by {intros, ring} : ∀ (α β γ : ℂ), β * (α * γ) = α * (β * γ))],
    apply integral_const_mul },
  { exact fact.mk zero_lt_one, },
end

/-- The Fourier coefficients of `B₀(x) = 1`. -/
lemma bernoulli_zero_fourier_coeff (n : ℤ) (hn : n ≠ 0):
  ∫ x in 0..1, e (-n) x * bernoulli_fun 0 x = 0 :=
by simpa using coefficient_recurrence 0 hn

/-- The `0`-th Fourier coefficient of `Bₖ(x)`. -/
lemma bernoulli_fourier_coeff_zero {k : ℕ} (hk : 1 ≤ k) :
  ∫ x in 0..1, e (-0) x * bernoulli_fun k x = 0 :=
begin
  simp_rw [fourier_coe_apply, neg_zero, int.cast_zero, mul_zero, zero_mul, zero_div, exp_zero,
    one_mul, interval_integral.integral_of_real, integral_bernoulli_fun_eq_zero _ hk, of_real_zero],
end

lemma bernoulli_fourier_coeff_eq {k : ℕ} (hk : 1 ≤ k) (n : ℤ) :
  ∫ x in 0..1, e (-n) x * bernoulli_fun k x = -k.factorial / (2 * π * I * n) ^ k :=
begin
  rcases eq_or_ne n 0 with rfl|hn,
  { rw [bernoulli_fourier_coeff_zero hk, int.cast_zero, mul_zero,
      zero_pow (by linarith : 0 < k), div_zero] },
  induction k with k h, -- no tidy way to induct starting at 1?
  { exfalso, linarith, },
  { rw coefficient_recurrence k.succ hn,
    rcases nat.eq_zero_or_pos k with rfl|hk',
    { simp only [nat.cast_one, tsub_self, neg_mul, one_mul, eq_self_iff_true, if_true,
        nat.factorial_one, pow_one, inv_I, mul_neg],
      rw [bernoulli_zero_fourier_coeff n hn, sub_zero, mul_one, div_neg, neg_div], },
    { rw [nat.succ_sub_one, nat.succ_eq_add_one, h (nat.one_le_of_lt hk')],
      split_ifs,
      { exfalso, contrapose! h_1, linarith,  },
      { rw [nat.factorial_succ, zero_sub, nat.cast_mul, pow_add, pow_one, neg_div,
          mul_neg, mul_neg, mul_neg, neg_neg, neg_mul, neg_mul, neg_mul, div_neg],
        field_simp [int.cast_ne_zero.mpr hn, I_ne_zero],
        ring_nf, } } }
end

end bernoulli_fourier_coeffs
