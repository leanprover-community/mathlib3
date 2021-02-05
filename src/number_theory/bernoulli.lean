/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card
<<<<<<< HEAD
=======
import algebra.big_operators.nat_antidiagonal
>>>>>>> master
import ring_theory.power_series.well_known

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, 1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ is even then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

Note however that this result is not yet formalised in Lean.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

Note that $B_1=+1/2$, meaning that we are using the $B_n^+$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).
To get the "minus" convention, just use `(-1)^n * bernoulli n`.

There is no particular reason that the `+` convention was used.
In some sense it's like choosing whether you want to sum over `fin n`
(so `j < n`) or sum over `j ≤ n` (or `nat.antidiagonal n`). Indeed
$$(t+1)\sum_{j\lt n}j^t=\sum_{k\leq t}\binom{t+1}{k}B_k^{-}n^{t+1-k}$$
and
$$(t+1)\sum_{j\leq n}j^t=\sum_{k\leq t}\binom{t+1}{k}B_k^{+}n^{t+1-k}.$$

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$.

## Main theorems

`sum_bernoulli : ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n`

## Todo

* `∑ k : fin n, n.binomial k * (-1)^k * bernoulli k = if n = 1 then 1 else 0`

* Bernoulli polynomials

* `∑ k : fin n, k ^ t =` the Bernoulli polynomial B_t evaluated at n

* `∑ k : fin n.succ, n.succ.choose k bernoulli_poly k X = n.succ * X ^ n` as polynomials
-/

open_locale big_operators
open nat
open finset

/-!

### Definitions

-/

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - ∑ k : fin n, n.choose k / (n - k + 1) * bernoulli k k.2)

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, (n.choose k) / (n - k + 1) * bernoulli k :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, (n.choose k) / (n - k + 1) * bernoulli k :=
by { rw [bernoulli_def', ← fin.sum_univ_eq_sum_range], refl }

lemma bernoulli_spec (n : ℕ) :
  ∑ k in finset.range n.succ, (n.choose (n - k) : ℚ) / (n - k + 1) * bernoulli k = 1 :=
begin
  rw [finset.sum_range_succ, bernoulli_def n, nat.sub_self],
  conv in (nat.choose _ (_ - _)) { rw choose_symm (le_of_lt (finset.mem_range.1 H)) },
  simp only [one_mul, cast_one, sub_self, sub_add_cancel, choose_zero_right, zero_add, div_one],
end

lemma bernoulli_spec' (n : ℕ) :
  ∑ k in finset.nat.antidiagonal n,
  ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli k.1 = 1 :=
begin
  refine ((nat.sum_antidiagonal_eq_sum_range_succ_mk _ n).trans _).trans (bernoulli_spec n),
  refine sum_congr rfl (λ x hx, _),
  rw mem_range_succ_iff at hx,
  simp [nat.add_sub_cancel' hx, cast_sub hx],
end

/-!

### Examples

-/

section examples

open finset

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl

@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 :=
begin
    rw [bernoulli_def, sum_range_one], norm_num
end

@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one],
  rw (show nat.choose 4 2 = 6, from dec_trivial), -- shrug
  norm_num,
end

end examples

open nat finset

@[simp] lemma sum_bernoulli (n : ℕ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n :=
begin
  cases n with n, { simp },
  rw [sum_range_succ, bernoulli_def],
  suffices : (n + 1 : ℚ) * ∑ k in range n, (n.choose k : ℚ) / (n - k + 1) * bernoulli k =
    ∑ x in range n, (n.succ.choose x : ℚ) * bernoulli x,
  { rw [← this, choose_succ_self_right], norm_cast, ring},
  simp_rw [mul_sum, ← mul_assoc],
  apply sum_congr rfl,
  intros k hk, replace hk := le_of_lt (mem_range.1 hk),
  rw ← cast_sub hk,
  congr',
  field_simp [show ((n - k : ℕ) : ℚ) + 1 ≠ 0, by {norm_cast, simp}],
  norm_cast,
  rw [mul_comm, nat.sub_add_eq_add_sub hk],
  exact choose_mul_succ_eq n k,
end

open power_series

theorem bernoulli_power_series :
  power_series.mk (λ n, (bernoulli n / nat.factorial n : ℚ)) * (exp ℚ - 1) = X * exp ℚ :=
begin
  ext n,
  -- constant coefficient is a special case
  cases n,
  { simp only [ring_hom.map_sub, constant_coeff_one, zero_mul, constant_coeff_exp, constant_coeff_X,
      coeff_zero_eq_constant_coeff, mul_zero, sub_self, ring_hom.map_mul] },
  rw [coeff_mul, mul_comm X, coeff_succ_mul_X],
  simp only [coeff_mk, coeff_one, coeff_exp, linear_map.map_sub, factorial,
    rat.algebra_map_rat_rat, nat.sum_antidiagonal_succ', if_pos],
  simp only [factorial, prod.snd, one_div, cast_succ, cast_one, cast_mul, ring_hom.id_apply,
    sub_zero, add_eq_zero_iff, if_false, zero_add, one_ne_zero,
    factorial, div_one, mul_zero, and_false, sub_self],
  apply eq_inv_of_mul_left_eq_one,
  rw sum_mul,
  convert bernoulli_spec' n using 1,
  apply sum_congr rfl,
  rintro ⟨i, j⟩ hn,
  rw nat.mem_antidiagonal at hn,
  subst hn,
  dsimp only,
  have hj : (j : ℚ) + 1 ≠ 0, by { norm_cast, linarith },
  have hj' : j.succ ≠ 0, by { show j + 1 ≠ 0, by linarith },
  have hnz : (j + 1 : ℚ) * nat.factorial j * nat.factorial i ≠ 0,
  { norm_cast at *,
    exact mul_ne_zero (mul_ne_zero hj (factorial_ne_zero j)) (factorial_ne_zero _), },
  field_simp [hj, hnz],
  rw [mul_comm _ (bernoulli i), mul_assoc],
  norm_cast,
  rw [mul_comm (j + 1) _, mul_div_assoc, ← mul_assoc, cast_mul, cast_mul, mul_div_mul_right _,
    add_choose, cast_dvd_char_zero],
  { apply factorial_mul_factorial_dvd_factorial_add, },
  { exact cast_ne_zero.mpr hj', },
end

--open nat
open ring_hom

theorem bernoulli_power_series :
(power_series.mk (λ n, ((bernoulli n) / (nat.factorial n) : ℚ))) * (power_series.exp ℚ - 1) =
  (X : power_series ℚ) * (exp ℚ) := sorry

@[to_additive]
lemma prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [comm_monoid M] (f : ℕ × ℕ → M) (n : ℕ) :
  ∏ ij in finset.nat.antidiagonal n, f ij = ∏ k in range n.succ, f (k, n - k) := sorry

/-- This lemma matches more generally than `finset.nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ←`. -/
@[to_additive]
lemma prod_antidiagonal_eq_prod_range_succ {M : Type*} [comm_monoid M] (f : ℕ → ℕ → M) (n : ℕ) :
  ∏ ij in finset.nat.antidiagonal n, f ij.1 ij.2 = ∏ k in range n.succ, f k (n - k) := sorry

noncomputable def eval_mul_hom (A : Type*) [comm_ring A] (a : A) : power_series A →+* power_series A :=
{
  to_fun :=   λ f, mk $ λ n, a^n * (coeff A n f),
  map_zero' := by {simp, ext, simp, },
  map_one' := by { simp, ext1, simp, split_ifs, rw [h, pow_zero], refl, },
  map_add' := by {intros, ext, norm_num, rw mul_add, },
  map_mul' := by {intros, ext, rw coeff_mul, simp, rw coeff_mul, rw mul_sum, apply sum_congr rfl,
            norm_num, intros b c H, rw <-H, rw pow_add, rw mul_assoc, rw ←mul_assoc (a^c) _ _,
            rw mul_comm (a^c) _, rw mul_assoc _ (a^c) _, ring, },
}

theorem exp_mul_exp_eq_exp_add (A : Type*) [comm_ring A] [algebra ℚ A] (a b : A) :
  (eval_mul_hom A a (exp A)) * (eval_mul_hom A b (exp A)) = (eval_mul_hom A (a + b) (exp A)) :=
begin
  ext,
  rw [coeff_mul, exp, eval_mul_hom, eval_mul_hom, eval_mul_hom], simp only [coeff_mk, coe_mk, factorial],
  { rw sum_antidiagonal_eq_sum_range_succ_mk, simp only [factorial], rw add_pow,
  rw sum_mul, apply sum_congr, refl, rintros x hx,
  rw mul_assoc (a^x * b ^ (n - x)) _ _, rw mul_assoc (a^x) _ _, rw ←mul_assoc _  (b ^ (n - x)) _,
  rw mul_comm _ (b^(n - x)), rw ←mul_assoc (a^x) _ _, rw ←mul_assoc (a^x) _ _,
  suffices f : (algebra_map ℚ A) (1 / ↑(x.factorial)) * (algebra_map ℚ A) (1 / ↑((n - x).factorial))
   = (↑(n.choose x) * (algebra_map ℚ A) (1 / ↑(n.factorial))),
  { rw ←f, rw mul_assoc, },
  rw ←map_nat_cast (algebra_map ℚ A) (n.choose x), rw ←map_mul, rw ←map_mul,
  refine ring_hom.congr_arg _ _, rw mul_one_div ↑(n.choose x) _, rw one_div_mul_one_div,
   symmetry, rw div_eq_iff, rw div_mul_eq_mul_div, rw one_mul, rw choose_eq_factorial_div_factorial,
   norm_cast, rw cast_dvd_char_zero,
   { apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx), },
   { apply mem_range_succ_iff.1 hx, },
   { rintros h, apply factorial_ne_zero n, rw cast_eq_zero.1 h, },
 },
end

lemma eval_mul_hom_zero (A : Type*) [comm_ring A] [algebra ℚ A] (f : power_series A) :
  eval_mul_hom A 0 f = (C A ((constant_coeff A) f) ) :=
begin
  rw eval_mul_hom, simp, ext, simp, rw power_series.coeff_C, split_ifs,
  rw h, simp,
  rw zero_pow' n h, rw zero_mul,
end

lemma eval_mul_hom_one (A : Type*) [comm_ring A] [algebra ℚ A] (f : power_series A) :
  eval_mul_hom A 1 f = f :=
begin
  rw eval_mul_hom, simp, ext, simp,
end

noncomputable def eval_neg_hom (A : Type*) [comm_ring A] : power_series A →+* power_series A :=
  eval_mul_hom A (-1 : A)

lemma sum_choose_neg_one : ∀ n : ℕ,
  ∑ k in finset.range n.succ, (n.choose k : ℚ) * (-1)^(n - k) = 0 := sorry

@[simp] lemma constant_coeff_exp (A : Type*) [comm_ring A] [algebra ℚ A] : constant_coeff A (exp A) = 1 := sorry

theorem exp_mul_exp_neg_eq_one (A : Type*) [comm_ring A] [algebra ℚ A] :
  (exp A) * (eval_neg_hom A (exp A)) = 1 :=
begin
  rw eval_neg_hom,
  conv_lhs { congr, rw ←eval_mul_hom_one A (exp A), },
  rw exp_mul_exp_eq_exp_add, simp, rw eval_mul_hom_zero, simp,
end

@[simp] lemma eval_neg_hom_X (A : Type*) [comm_ring A] : eval_neg_hom ℚ X = -X :=
begin
  rw eval_neg_hom, ext, simp, rw coeff_X, split_ifs, rw h, rw eval_mul_hom, simp,
  rw eval_mul_hom, simp, right, rw coeff_X, split_ifs, refl,
end

theorem bernoulli_odd_eq_zero : ∀ n : ℕ, (n % 2 = 1 ∧ 1 < n) → bernoulli n = 0 :=
begin
  have f := bernoulli_power_series,
  have g : eval_neg_hom ℚ (mk (λ (n : ℕ), bernoulli n / ↑(n.factorial)) * (exp ℚ - 1)) * (exp ℚ) =
    (eval_neg_hom ℚ (X * exp ℚ)) * (exp ℚ),
    { rw mul_eq_mul_right_iff, left,
      congr, assumption, },
    rw [map_mul, map_sub, map_one, map_mul, mul_assoc, sub_mul, mul_assoc ((eval_neg_hom ℚ) X) _ _,
    mul_comm ((eval_neg_hom ℚ) (exp ℚ)) (exp ℚ), exp_mul_exp_neg_eq_one ℚ, eval_neg_hom_X ℚ, mul_one,
     one_mul] at g,
  suffices h : (mk (λ (n : ℕ), bernoulli n / ↑(n.factorial)) - (eval_neg_hom ℚ) (mk (λ (n : ℕ),
    bernoulli n / ↑(n.factorial))) ) * (exp ℚ - 1) = X * (exp ℚ - 1),
    simp at h, cases h,
    { rw eval_neg_hom at h, rw eval_mul_hom at h, simp at h, rw power_series.ext_iff at h, simp at h,
     rintros n hn, cases hn with hn1 hn2, specialize h n, rw coeff_X n at h, split_ifs at h,
     { rw h_1 at hn2, exfalso, simp at *, norm_num at *, },
     rw ←mul_div_assoc at h, rw sub_eq_zero_iff_eq at h,
     rw div_eq_iff at h,
     { rw div_mul_cancel at h, {rw neg_one_pow_eq_pow_mod_two at h, rw hn1 at h,
     simp at *, rw eq_zero_of_neg_eq h.symm, },
     { rintros h, apply factorial_ne_zero n, rw cast_eq_zero.1 h, }, },
     { rintros h, apply factorial_ne_zero n, rw cast_eq_zero.1 h, },
    },
  { rintros n ⟨hn1, hn2⟩, exfalso, rw sub_eq_zero_iff_eq at h, rw power_series.ext_iff at h,
    simp at h, specialize h n, split_ifs at h,
    { rw h_1 at hn2, norm_num at *, },
    apply factorial_ne_zero n, simp at h, assumption, },
  { rw sub_mul, rw f, rw mul_sub X _ _, simp,
    have f : (exp ℚ - 1) = -(1 - exp ℚ) := by simp,
    rw f, rw ←neg_neg X, rw ←g, rw neg_mul_eq_mul_neg, },
