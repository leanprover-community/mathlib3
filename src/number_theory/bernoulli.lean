/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card
import algebra.big_operators.nat_antidiagonal
import ring_theory.power_series.well_known

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, -1/2, 1/6, 0, -1/30, \ldots)$ are
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

Note that $B_1=-1/2$, meaning that we are using the $B_n^-$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$. Note that this is the definition
for positive Bernoulli numbers, which we call `bernoulli'`. The negative Bernoulli numbers are
then defined as `bernoulli = (-1)^n * bernoulli'`.

## Main theorems

`sum_bernoulli : ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = 0`

-/

open_locale big_operators
open nat
open finset
open_locale nat

/-!

### Definitions

-/

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli' : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli', 1 - ∑ k : fin n, n.choose k / (n - k + 1) * bernoulli' k k.2)

lemma bernoulli'_def' (n : ℕ) :
  bernoulli' n = 1 - ∑ k : fin n, (n.choose k) / (n - k + 1) * bernoulli' k :=
well_founded.fix_eq _ _ _

lemma bernoulli'_def (n : ℕ) :
  bernoulli' n = 1 - ∑ k in finset.range n, (n.choose k) / (n - k + 1) * bernoulli' k :=
by { rw [bernoulli'_def', ← fin.sum_univ_eq_sum_range], refl }

lemma bernoulli'_spec (n : ℕ) :
  ∑ k in finset.range n.succ, (n.choose (n - k) : ℚ) / (n - k + 1) * bernoulli' k = 1 :=
begin
  rw [finset.sum_range_succ, bernoulli'_def n, nat.sub_self],
  conv in (nat.choose _ (_ - _)) { rw choose_symm (le_of_lt (finset.mem_range.1 H)) },
  simp only [one_mul, cast_one, sub_self, sub_add_cancel, choose_zero_right, zero_add, div_one],
end

lemma bernoulli'_spec' (n : ℕ) :
  ∑ k in finset.nat.antidiagonal n,
  ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli' k.1 = 1 :=
begin
  refine ((nat.sum_antidiagonal_eq_sum_range_succ_mk _ n).trans _).trans (bernoulli'_spec n),
  refine sum_congr rfl (λ x hx, _),
  rw mem_range_succ_iff at hx,
  simp [nat.add_sub_cancel' hx, cast_sub hx],
end

/-!

### Examples

-/

section examples

open finset

@[simp] lemma bernoulli'_zero  : bernoulli' 0 = 1   := rfl

@[simp] lemma bernoulli'_one   : bernoulli' 1 = 1/2 :=
begin
    rw [bernoulli'_def, sum_range_one], norm_num
end

@[simp] lemma bernoulli'_two   : bernoulli' 2 = 1/6 :=
begin
  rw [bernoulli'_def, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli'_three : bernoulli' 3 = 0   :=
begin
  rw [bernoulli'_def, sum_range_succ, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli'_four  : bernoulli' 4 = -1/30 :=
begin
  rw [bernoulli'_def, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one],
  rw (show nat.choose 4 2 = 6, from dec_trivial), -- shrug
  norm_num,
end

end examples

open nat finset

@[simp] lemma sum_bernoulli' (n : ℕ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli' k = n :=
begin
  cases n with n, { simp },
  rw [sum_range_succ, bernoulli'_def],
  suffices : (n + 1 : ℚ) * ∑ k in range n, (n.choose k : ℚ) / (n - k + 1) * bernoulli' k =
    ∑ x in range n, (n.succ.choose x : ℚ) * bernoulli' x,
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

theorem bernoulli'_power_series :
  power_series.mk (λ n, (bernoulli' n / n! : ℚ)) * (exp ℚ - 1) = X * exp ℚ :=
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
  convert bernoulli'_spec' n using 1,
  apply sum_congr rfl,
  rintro ⟨i, j⟩ hn,
  rw nat.mem_antidiagonal at hn,
  subst hn,
  dsimp only,
  have hj : (j : ℚ) + 1 ≠ 0, by { norm_cast, linarith },
  have hj' : j.succ ≠ 0, by { show j + 1 ≠ 0, by linarith },
  have hnz : (j + 1 : ℚ) * j! * i! ≠ 0,
  { norm_cast at *,
    exact mul_ne_zero (mul_ne_zero hj (factorial_ne_zero j)) (factorial_ne_zero _), },
  field_simp [hj, hnz],
  rw [mul_comm _ (bernoulli' i), mul_assoc],
  norm_cast,
  rw [mul_comm (j + 1) _, mul_div_assoc, ← mul_assoc, cast_mul, cast_mul, mul_div_mul_right _,
    add_choose, cast_dvd_char_zero],
  { apply factorial_mul_factorial_dvd_factorial_add, },
  { exact cast_ne_zero.mpr hj', },
end

open ring_hom

/-- Odd Bernoulli numbers (greater than 1) are zero. -/
theorem bernoulli'_odd_eq_zero {n : ℕ} (h_odd : odd n) (hlt : 1 < n) : bernoulli' n = 0 :=
begin
  have f := bernoulli'_power_series,
  have g : eval_neg_hom (mk (λ (n : ℕ), bernoulli' n / ↑(n!)) * (exp ℚ - 1)) * (exp ℚ) =
    (eval_neg_hom (X * exp ℚ)) * (exp ℚ) := by congr',
  rw [map_mul, map_sub, map_one, map_mul, mul_assoc, sub_mul, mul_assoc (eval_neg_hom X) _ _,
    mul_comm (eval_neg_hom (exp ℚ)) (exp ℚ), exp_mul_exp_neg_eq_one, eval_neg_hom_X, mul_one,
    one_mul] at g,
  suffices h : (mk (λ (n : ℕ), bernoulli' n / ↑(n!)) - eval_neg_hom (mk (λ (n : ℕ),
    bernoulli' n / ↑(n!))) ) * (exp ℚ - 1) = X * (exp ℚ - 1),
  { rw [mul_eq_mul_right_iff] at h,
    cases h,
    { simp only [eval_neg_hom, rescale, coeff_mk, coe_mk, power_series.ext_iff,
        coeff_mk, linear_map.map_sub] at h,
      specialize h n,
      rw coeff_X n at h,
      split_ifs at h with h2,
      { rw h2 at hlt, exfalso, exact lt_irrefl _ hlt, },
      have hn : (n! : ℚ) ≠ 0, { simp [factorial_ne_zero], },
      rw [←mul_div_assoc, sub_eq_zero_iff_eq, div_eq_iff hn, div_mul_cancel _ hn,
        neg_one_pow_of_odd h_odd, neg_mul_eq_neg_mul_symm, one_mul] at h,
      exact eq_zero_of_neg_eq h.symm, },
    { exfalso,
      rw [power_series.ext_iff] at h,
      specialize h 1,
      simpa using h, }, },
  { rw [sub_mul, f, mul_sub X, mul_one, sub_right_inj, ←neg_sub, ←neg_neg X, ←g,
      neg_mul_eq_mul_neg], },
end

/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli (n : ℕ) : ℚ := (-1)^n * (bernoulli' n)

lemma bernoulli'_eq_neg_one_pow_mul_bernoulli (n : ℕ) : bernoulli' n = (-1)^n * bernoulli n :=
begin
  rw [bernoulli],
  ring,
  simp only [←pow_mul, mul_comm n 2, pow_mul, one_pow, neg_one_pow_two, mul_one],
end

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1 := rfl

@[simp] lemma bernoulli_one   : bernoulli 1 = -1/2 :=
by norm_num [bernoulli, bernoulli'_one]

theorem bernoulli_eq_bernoulli' {n : ℕ} (hn : n ≠ 1) : bernoulli n = bernoulli' n :=
begin
  by_cases n = 0,
  { rw [h, bernoulli'_zero, bernoulli_zero] },
  { rw [bernoulli, neg_one_pow_eq_pow_mod_two],
    by_cases k : n % 2 = 1,
    { have f : 1 < n := one_lt_iff_ne_zero_and_ne_one.2 ⟨h, hn⟩,
      simp [bernoulli'_odd_eq_zero (odd_iff.2 k) f] },
    rw mod_two_ne_one at k, simp [k] }
end

@[simp] theorem sum_bernoulli (n : ℕ) ( h : 2 ≤ n ) :
  ∑ k in range n, (n.choose k : ℚ) * bernoulli k = 0 :=
begin
  cases n, norm_num at h,
  cases n, norm_num at h,
  rw [sum_range_succ', bernoulli_zero, mul_one, choose_zero_right, cast_one,
    sum_range_succ', bernoulli_one, choose_one_right],
  suffices : ∑ (i : ℕ) in range n, ↑((n + 2).choose (i + 2)) * bernoulli (i + 2) = n/2,
  { rw [this, cast_succ, cast_succ], ring },
  have f := sum_bernoulli' n.succ.succ,
  simp only [sum_range_succ', one_div, bernoulli'_one, cast_succ, mul_one, cast_one, add_left_inj,
    choose_zero_right, bernoulli'_zero, zero_add, choose_one_right, ← eq_sub_iff_add_eq] at f,
  convert f,
  { ext x, rw bernoulli_eq_bernoulli' (succ_ne_zero x ∘ succ.inj) },
  { ring },
end

theorem bernoulli_power_series :
  power_series.mk (λ n, (bernoulli n / n! : ℚ)) * (exp ℚ - 1) = X :=
begin
    suffices f : eval_neg_hom (power_series.mk (λ n, (bernoulli n / nat.factorial n : ℚ)) *
    (exp ℚ - 1)) = eval_neg_hom X,
  { suffices g : function.injective eval_neg_hom,
    { rwa g.eq_iff at f, },
    apply rescale_injective,
    norm_num, },
  simp only [map_one, map_mul, eval_neg_hom_X, map_sub],
  suffices h:
    eval_neg_hom (mk (λ (n : ℕ), bernoulli n / ↑n!)) * (eval_neg_hom (exp ℚ) - 1) * (- exp ℚ)
    = -X * (- exp ℚ),
  { have hexp : - exp ℚ ≠ 0, {
    rw [exp],
    simp only [power_series.ext_iff, linear_map.map_zero, one_div, coeff_mk, coeff_one,
    ring_hom.id_apply, linear_map.map_sub, ne.def, not_forall,
    rat.algebra_map_rat_rat],
    use 1,
    simp only [factorial_one, coeff_mk, linear_map.map_neg, cast_one, inv_one, not_false_iff,
      neg_eq_zero, one_ne_zero],
  },
   apply mul_right_cancel' hexp h, },
  { rw [mul_assoc],
    have he: (eval_neg_hom (exp ℚ) - 1) * (- exp ℚ) = ((exp ℚ) - 1),
    { ring,
      simp [exp_mul_exp_neg_eq_one],
      ring,
    },
    rw [he],
    simp only [eval_neg_hom, rescale, neg_mul_eq_neg_mul_symm, coeff_mk, coe_mk,
      mul_neg_eq_neg_mul_symm, neg_neg, ←mul_div_assoc, ←bernoulli'_of_bernoulli,
      bernoulli'_power_series], },
end
