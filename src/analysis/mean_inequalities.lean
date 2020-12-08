/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import analysis.convex.specific_functions
import analysis.special_functions.pow
import data.real.conjugate_exponents
import tactic.nth_rewrite
import measure_theory.integration

/-!
# Mean value inequalities

In this file we prove several inequalities, including AM-GM inequality, Young's inequality,
Hölder inequality, and Minkowski inequality.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `real` namespace, and a version for
`nnreal`-valued functions is in the `nnreal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.

### Generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`fpow_arith_mean_le_arith_mean_fpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It can be used to prove Hölder's
inequality (see below) but we use a different proof.

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `real`, `nnreal` and `ennreal`.

There are at least two short proofs of this inequality. In one proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. We use a different proof deducing this inequality
from the generalized mean inequality for well-chosen vectors and weights.

Hölder's inequality for the Lebesgue integral of ennreal and nnreal functions: xe prove
`∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q` conjugate real exponents
and `α→(e)nnreal` functions in two cases,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ennreal functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : nnreal functions.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `real`, `nnreal` and `ennreal`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `strict_convex_on` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.
- prove integral versions of these inequalities.

-/

universes u v

open finset
open_locale classical nnreal big_operators
noncomputable theory

variables {ι : Type u} (s : finset ι)

namespace real

/-- AM-GM inequality: the geometric mean is less than or equal to the arithmetic mean, weighted version
for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
  (∏ i in s, (z i) ^ (w i)) ≤ ∑ i in s, w i * z i :=
begin
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0,
  { rcases A with ⟨i, his, hzi, hwi⟩,
    rw [prod_eq_zero his],
    { exact sum_nonneg (λ j hj, mul_nonneg (hw j hj) (hz j hj)) },
    { rw hzi, exact zero_rpow hwi } },
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
  { simp only [not_exists, not_and, ne.def, not_not] at A,
    have := convex_on_exp.map_sum_le hw hw' (λ i _, set.mem_univ $ log (z i)),
    simp only [exp_sum, (∘), smul_eq_mul, mul_comm (w _) (log _)] at this,
    convert this using 1; [apply prod_congr rfl, apply sum_congr rfl]; intros i hi,
    { cases eq_or_lt_of_le (hz i hi) with hz hz,
      { simp [A i hi hz.symm] },
      { exact rpow_def_of_pos hz _ } },
    { cases eq_or_lt_of_le (hz i hi) with hz hz,
      { simp [A i hi hz.symm] },
      { rw [exp_log hz] } } }
end

theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (n : ℕ) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
(convex_on_pow n).map_sum_le hw hw' hz

theorem pow_arith_mean_le_arith_mean_pow_of_even (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) {n : ℕ} (hn : even n) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
(convex_on_pow_of_even hn).map_sum_le hw hw' (λ _ _, trivial)

theorem fpow_arith_mean_le_arith_mean_fpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) (m : ℤ) :
  (∑ i in s, w i * z i) ^ m ≤ ∑ i in s, (w i * z i ^ m) :=
(convex_on_fpow m).map_sum_le hw hw' hz

theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, (w i * z i ^ p) :=
(convex_on_rpow hp).map_sum_le hw hw' hz

theorem arith_mean_le_rpow_mean (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
  ∑ i in s, w i * z i ≤ (∑ i in s, (w i * z i ^ p)) ^ (1 / p) :=
begin
  have : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  rw [← rpow_le_rpow_iff _ _ this, ← rpow_mul, one_div_mul_cancel (ne_of_gt this), rpow_one],
  exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp,
  all_goals { apply_rules [sum_nonneg, rpow_nonneg_of_nonneg],
    intros i hi,
    apply_rules [mul_nonneg, rpow_nonneg_of_nonneg, hw i hi, hz i hi] },
end

end real

namespace nnreal

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for `nnreal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) :
  (∏ i in s, (z i) ^ (w i:ℝ)) ≤ ∑ i in s, w i * z i :=
by exact_mod_cast real.geom_mean_le_arith_mean_weighted _ _ _ (λ i _, (w i).coe_nonneg)
  (by assumption_mod_cast) (λ i _, (z i).coe_nonneg)

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for two `nnreal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) :
  w₁ + w₂ = 1 → p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) ≤ w₁ * p₁ + w₂ * p₂ :=
by simpa only [fin.prod_univ_succ, fin.sum_univ_succ, fin.prod_univ_zero, fin.sum_univ_zero,
  fin.cons_succ, fin.cons_zero, add_zero, mul_one]
using geom_mean_le_arith_mean_weighted (univ : finset (fin 2))
  (fin.cons w₁ $ fin.cons w₂ fin_zero_elim) (fin.cons p₁ $ fin.cons p₂ $ fin_zero_elim)

theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) :
  w₁ + w₂ + w₃ = 1 → p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) * p₃ ^ (w₃:ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
by simpa only  [fin.prod_univ_succ, fin.sum_univ_succ, fin.prod_univ_zero, fin.sum_univ_zero,
  fin.cons_succ, fin.cons_zero, add_zero, mul_one, ← add_assoc, mul_assoc]
using geom_mean_le_arith_mean_weighted (univ : finset (fin 3))
  (fin.cons w₁ $ fin.cons w₂ $ fin.cons w₃ fin_zero_elim)
  (fin.cons p₁ $ fin.cons p₂ $ fin.cons p₃ fin_zero_elim)

theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0) :
  w₁ + w₂ + w₃ + w₄ = 1 → p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) * p₃ ^ (w₃:ℝ)* p₄ ^ (w₄:ℝ) ≤
    w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
by simpa only  [fin.prod_univ_succ, fin.sum_univ_succ, fin.prod_univ_zero, fin.sum_univ_zero,
  fin.cons_succ, fin.cons_zero, add_zero, mul_one, ← add_assoc, mul_assoc]
using geom_mean_le_arith_mean_weighted (univ : finset (fin 4))
  (fin.cons w₁ $ fin.cons w₂ $ fin.cons w₃ $ fin.cons w₄ fin_zero_elim)
  (fin.cons p₁ $ fin.cons p₂ $ fin.cons p₃ $ fin.cons p₄ fin_zero_elim)

/-- Weighted generalized mean inequality, version sums over finite sets, with `ℝ≥0`-valued
functions and natural exponent. -/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) (n : ℕ) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
by exact_mod_cast real.pow_arith_mean_le_arith_mean_pow s _ _ (λ i _, (w i).coe_nonneg)
  (by exact_mod_cast hw') (λ i _, (z i).coe_nonneg) n

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) {p : ℝ}
  (hp : 1 ≤ p) :
  (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, (w i * z i ^ p) :=
by exact_mod_cast real.rpow_arith_mean_le_arith_mean_rpow s _ _ (λ i _, (w i).coe_nonneg)
  (by exact_mod_cast hw') (λ i _, (z i).coe_nonneg) hp

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0) (hw' : w₁ + w₂ = 1) {p : ℝ}
  (hp : 1 ≤ p) :
  (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p :=
begin
  have h := rpow_arith_mean_le_arith_mean_rpow (univ : finset (fin 2))
    (fin.cons w₁ $ fin.cons w₂ fin_zero_elim) (fin.cons z₁ $ fin.cons z₂ $ fin_zero_elim) _ hp,
  { simpa [fin.sum_univ_succ, fin.sum_univ_zero, fin.cons_succ, fin.cons_zero] using h, },
  { simp [hw', fin.sum_univ_succ, fin.sum_univ_zero, fin.cons_succ, fin.cons_zero], },
end

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem arith_mean_le_rpow_mean (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) {p : ℝ}
  (hp : 1 ≤ p) :
  ∑ i in s, w i * z i ≤ (∑ i in s, (w i * z i ^ p)) ^ (1 / p) :=
by exact_mod_cast real.arith_mean_le_rpow_mean s _ _ (λ i _, (w i).coe_nonneg)
  (by exact_mod_cast hw') (λ i _, (z i).coe_nonneg) hp

end nnreal

namespace real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
  (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
nnreal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ $
  nnreal.coe_eq.1 $ by assumption

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
  (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
nnreal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ $
  nnreal.coe_eq.1 $ by assumption

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁)
  (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
  (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
nnreal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩
  ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ $ nnreal.coe_eq.1 $ by assumption

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a^p / p + b^q / q :=
by simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul]
  using geom_mean_le_arith_mean2_weighted hpq.one_div_nonneg hpq.symm.one_div_nonneg
    (rpow_nonneg_of_nonneg ha p) (rpow_nonneg_of_nonneg hb q) hpq.inv_add_inv_conj

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ (abs a)^p / p + (abs b)^q / q :=
calc a * b ≤ abs (a * b)                   : le_abs_self (a * b)
       ... = abs a * abs b                 : abs_mul a b
       ... ≤ (abs a)^p / p + (abs b)^q / q :
  real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

end real

namespace nnreal

/-- Young's inequality, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators.  -/
theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
  a * b ≤ a^(p:ℝ) / p + b^(q:ℝ) / q :=
real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg ⟨hp, nnreal.coe_eq.2 hpq⟩

/-- Young's inequality, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a b : ℝ≥0) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a ^ p / nnreal.of_real p + b ^ q / nnreal.of_real q :=
begin
  nth_rewrite 0 ←coe_of_real p hpq.nonneg,
  nth_rewrite 0 ←coe_of_real q hpq.symm.nonneg,
  exact young_inequality a b hpq.one_lt_nnreal hpq.inv_add_inv_conj_nnreal,
end

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (f i) ^ p) ^ (1 / p) * (∑ i in s, (g i) ^ q) ^ (1 / q) :=
begin
  -- Let `G=∥g∥_q` be the `L_q`-norm of `g`.
  set G := (∑ i in s, (g i) ^ q) ^ (1 / q),
  have hGq : G ^ q = ∑ i in s, (g i) ^ q,
  { rw [← rpow_mul, one_div_mul_cancel hpq.symm.ne_zero, rpow_one], },
  -- First consider the trivial case `∥g∥_q=0`
  by_cases hG : G = 0,
  { rw [hG, sum_eq_zero, mul_zero],
    intros i hi,
    simp only [rpow_eq_zero_iff, sum_eq_zero_iff] at hG,
    simp [(hG.1 i hi).1] },
  { -- Move power from right to left
    rw [← div_le_iff hG, sum_div],
    -- Now the inequality follows from the weighted generalized mean inequality
    -- with weights `w_i` and numbers `z_i` given by the following formulas.
    set w : ι → ℝ≥0 := λ i, (g i) ^ q / G ^ q,
    set z : ι → ℝ≥0 := λ i, f i * (G / g i) ^ (q / p),
    -- Show that the sum of weights equals one
    have A : ∑ i in s, w i = 1,
    { rw [← sum_div, hGq, div_self],
      simpa [rpow_eq_zero_iff, hpq.symm.ne_zero] using hG },
    -- LHS of the goal equals LHS of the weighted generalized mean inequality
    calc (∑ i in s, f i * g i / G) = (∑ i in s, w i * z i) :
      begin
        refine sum_congr rfl (λ i hi, _),
        have : q - q / p = 1, by field_simp [hpq.ne_zero, hpq.symm.mul_eq_add],
        dsimp only [w, z],
        rw [← div_rpow, mul_left_comm, mul_div_assoc, ← @inv_div _ _ _ G, inv_rpow,
          ← div_eq_mul_inv, ← rpow_sub']; simp [this]
      end
    -- Apply the generalized mean inequality
    ... ≤ (∑ i in s, w i * (z i) ^ p) ^ (1 / p) :
      nnreal.arith_mean_le_rpow_mean s w z A (le_of_lt hpq.one_lt)
    -- Simplify the right hand side. Terms with `g i ≠ 0` are equal to `(f i) ^ p`,
    -- the others are zeros.
    ... ≤ (∑ i in s, (f i) ^ p) ^ (1 / p) :
      begin
        refine rpow_le_rpow (sum_le_sum (λ i hi, _)) hpq.one_div_nonneg,
        dsimp only [w, z],
        rw [mul_rpow, mul_left_comm, ← rpow_mul _ _ p, div_mul_cancel _ hpq.ne_zero, div_rpow,
          div_mul_div, mul_comm (G ^ q), mul_div_mul_right],
        { nth_rewrite 1 [← mul_one ((f i) ^ p)],
          exact canonically_ordered_semiring.mul_le_mul (le_refl _) (div_self_le _) },
        { simpa [hpq.symm.ne_zero] using hG }
      end }
end

/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i in s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
theorem is_greatest_Lp (f : ι → ℝ≥0) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  is_greatest ((λ g : ι → ℝ≥0, ∑ i in s, f i * g i) ''
    {g | ∑ i in s, (g i)^q ≤ 1}) ((∑ i in s, (f i)^p) ^ (1 / p)) :=
begin
  split,
  { use λ i, ((f i) ^ p / f i / (∑ i in s, (f i) ^ p) ^ (1 / q)),
    by_cases hf : ∑ i in s, (f i)^p = 0,
    { simp [hf, hpq.ne_zero, hpq.symm.ne_zero] },
    { have A : p + q - q ≠ 0, by simp [hpq.ne_zero],
      have B : ∀ y : ℝ≥0, y * y^p / y = y^p,
      { refine λ y, mul_div_cancel_left_of_imp (λ h, _),
        simpa [h, hpq.ne_zero] },
      simp only [set.mem_set_of_eq, div_rpow, ← sum_div, ← rpow_mul,
        div_mul_cancel _ hpq.symm.ne_zero, rpow_one, div_le_iff hf, one_mul, hpq.mul_eq_add,
        ← rpow_sub' _ A, _root_.add_sub_cancel, le_refl, true_and, ← mul_div_assoc, B],
      rw [div_eq_iff, ← rpow_add hf, hpq.inv_add_inv_conj, rpow_one],
      simpa [hpq.symm.ne_zero] using hf } },
  { rintros _ ⟨g, hg, rfl⟩,
    apply le_trans (inner_le_Lp_mul_Lq s f g hpq),
    simpa only [mul_one] using canonically_ordered_semiring.mul_le_mul (le_refl _)
      (nnreal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) }
end

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `nnreal`-valued functions. -/
theorem Lp_add_le (f g : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
    (∑ i in s, (f i) ^ p) ^ (1 / p) + (∑ i in s, (g i) ^ p) ^ (1 / p) :=
begin
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with rfl|hp, { simp [finset.sum_add_distrib] },
  have hpq := real.is_conjugate_exponent_conjugate_exponent hp,
  have := is_greatest_Lp s (f + g) hpq,
  simp only [pi.add_apply, add_mul, sum_add_distrib] at this,
  rcases this.1 with ⟨φ, hφ, H⟩,
  rw ← H,
  exact add_le_add ((is_greatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩)
    ((is_greatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)
end

end nnreal

namespace real

variables (f g : ι → ℝ)  {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : is_conjugate_exponent p q) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (abs $ f i)^p) ^ (1 / p) * (∑ i in s, (abs $ g i)^q) ^ (1 / q) :=
begin
  have := nnreal.coe_le_coe.2 (nnreal.inner_le_Lp_mul_Lq s (λ i, ⟨_, abs_nonneg (f i)⟩)
    (λ i, ⟨_, abs_nonneg (g i)⟩) hpq),
  push_cast at this,
  refine le_trans (sum_le_sum $ λ i hi, _) this,
  simp only [← abs_mul, le_abs_self]
end

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
  (∑ i in s, (abs $ f i + g i) ^ p) ^ (1 / p) ≤
    (∑ i in s, (abs $ f i) ^ p) ^ (1 / p) + (∑ i in s, (abs $ g i) ^ p) ^ (1 / p) :=
begin
  have := nnreal.coe_le_coe.2 (nnreal.Lp_add_le s (λ i, ⟨_, abs_nonneg (f i)⟩)
    (λ i, ⟨_, abs_nonneg (g i)⟩) hp),
  push_cast at this,
  refine le_trans (rpow_le_rpow _ (sum_le_sum $ λ i hi, _) _) this;
    simp [sum_nonneg, rpow_nonneg_of_nonneg, abs_nonneg, le_trans zero_le_one hp, abs_add,
      rpow_le_rpow]
end

variables {f g}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : is_conjugate_exponent p q)
  (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (f i)^p) ^ (1 / p) * (∑ i in s, (g i)^q) ^ (1 / q) :=
by convert inner_le_Lp_mul_Lq s f g hpq using 3; apply sum_congr rfl; intros i hi;
  simp only [abs_of_nonneg, hf i hi, hg i hi]

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued nonnegative
functions. -/
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
  (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
    (∑ i in s, (f i) ^ p) ^ (1 / p) + (∑ i in s, (g i) ^ p) ^ (1 / p) :=
by convert Lp_add_le s f g hp using 2 ; [skip, congr' 1, congr' 1];
  apply sum_congr rfl; intros i hi; simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

end real

namespace ennreal

/-- Young's inequality, `ennreal` version with real conjugate exponents. -/
theorem young_inequality (a b : ennreal) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a ^ p / ennreal.of_real p + b ^ q / ennreal.of_real q :=
begin
  by_cases h : a = ⊤ ∨ b = ⊤,
  { refine le_trans le_top (le_of_eq _),
    repeat {rw ennreal.div_def},
    cases h; rw h; simp [h, hpq.pos, hpq.symm.pos], },
  push_neg at h, -- if a ≠ ⊤ and b ≠ ⊤, use the nnreal version: nnreal.young_inequality_real
  rw [←coe_to_nnreal h.left, ←coe_to_nnreal h.right, ←coe_mul,
    coe_rpow_of_nonneg _ hpq.nonneg, coe_rpow_of_nonneg _ hpq.symm.nonneg, ennreal.of_real,
    ennreal.of_real, ←@coe_div (nnreal.of_real p) _ (by simp [hpq.pos]),
    ←@coe_div (nnreal.of_real q) _ (by simp [hpq.symm.pos]), ←coe_add, coe_le_coe],
  exact nnreal.young_inequality_real a.to_nnreal b.to_nnreal hpq,
end

variables (f g : ι → ennreal)  {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ennreal`-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  by_cases H : (∑ i in s, (f i)^p) ^ (1/p) = 0 ∨ (∑ i in s, (g i)^q) ^ (1/q) = 0,
  { replace H : (∀ i ∈ s, f i = 0) ∨ (∀ i ∈ s, g i = 0),
      by simpa [ennreal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
                sum_eq_zero_iff_of_nonneg] using H,
    have : ∀ i ∈ s, f i * g i = 0 := λ i hi, by cases H; simp [H i hi],
    have : (∑ i in s, f i * g i) = (∑ i in s, 0) := sum_congr rfl this,
    simp [this] },
  push_neg at H,
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^q) ^ (1/q) = ⊤,
  { cases H'; simp [H', -one_div, H] },
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
              ennreal.sum_eq_top_iff, not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@nnreal.inner_le_Lp_mul_Lq _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _ _ hpq),
  simp [← ennreal.coe_rpow_of_nonneg, le_of_lt (hpq.pos), le_of_lt (hpq.one_div_pos),
             le_of_lt (hpq.symm.pos), le_of_lt (hpq.symm.one_div_pos)] at this,
  convert this using 1;
  [skip, congr' 2];
  [skip, skip, simp, skip, simp];
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi, -with_zero.coe_mul,
    with_top.coe_mul.symm] },
end

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ennreal` valued nonnegative
functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^p) ^ (1/p) = ⊤,
  { cases H'; simp [H', -one_div] },
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm pos, pos, ennreal.sum_eq_top_iff,
              not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@nnreal.Lp_add_le _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _  hp),
  push_cast [← ennreal.coe_rpow_of_nonneg, le_of_lt (pos), le_of_lt (one_div_pos.2 pos)] at this,
  convert this using 2;
  [skip, congr' 1, congr' 1];
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi] }
end

end ennreal

section lintegral
/-!
### Hölder's inequality for the Lebesgue integral of ennreal and nnreal functions

We prove `∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q`
conjugate real exponents and `α→(e)nnreal` functions in several cases, the first two being useful
only to prove the more general results:
* `ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one` : ennreal functions for which the
    integrals on the right are equal to 1,
* `ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top` : ennreal functions for which the
    integrals on the right are neither ⊤ nor 0,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ennreal functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : nnreal functions.
-/

open measure_theory
variables {α : Type*} [measurable_space α] {μ : measure α}

namespace ennreal

lemma lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : ℝ} (hpq : p.is_conjugate_exponent q)
  {f g : α → ennreal} (hf : measurable f) (hg : measurable g)
  (hf_norm : ∫⁻ a, (f a)^p ∂μ = 1) (hg_norm : ∫⁻ a, (g a)^q ∂μ = 1) :
  ∫⁻ a, (f * g) a ∂μ ≤ 1 :=
begin
  calc ∫⁻ (a : α), ((f * g) a) ∂μ
      ≤ ∫⁻ (a : α), ((f a)^p / ennreal.of_real p + (g a)^q / ennreal.of_real q) ∂μ :
    lintegral_mono (λ a, young_inequality (f a) (g a) hpq)
  ... = 1 :
  begin
    simp_rw [div_def],
    rw lintegral_add,
    { rw [lintegral_mul_const _ hf.ennreal_rpow_const, lintegral_mul_const _ hg.ennreal_rpow_const,
        hf_norm, hg_norm, ←ennreal.div_def, ←ennreal.div_def, hpq.inv_add_inv_conj_ennreal], },
    { exact hf.ennreal_rpow_const.ennreal_mul measurable_const, },
    { exact hg.ennreal_rpow_const.ennreal_mul measurable_const, },
  end
end

/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p`-/
def fun_mul_inv_snorm (f : α → ennreal) (p : ℝ) (μ : measure α) : α → ennreal :=
λ a, (f a) * ((∫⁻ c, (f c) ^ p ∂μ) ^ (1 / p))⁻¹

lemma fun_eq_fun_mul_inv_snorm_mul_snorm {p : ℝ} (f : α → ennreal)
  (hf_nonzero : ∫⁻ a, (f a) ^ p ∂μ ≠ 0) (hf_top : ∫⁻ a, (f a) ^ p ∂μ ≠ ⊤) {a : α} :
  f a = (fun_mul_inv_snorm f p μ a) * (∫⁻ c, (f c)^p ∂μ)^(1/p) :=
by simp [fun_mul_inv_snorm, mul_assoc, inv_mul_cancel, hf_nonzero, hf_top]

lemma fun_mul_inv_snorm_rpow {p : ℝ} (hp0 : 0 < p) {f : α → ennreal} {a : α} :
  (fun_mul_inv_snorm f p μ a) ^ p = (f a)^p * (∫⁻ c, (f c) ^ p ∂μ)⁻¹ :=
begin
  rw [fun_mul_inv_snorm, mul_rpow_of_nonneg _ _ (le_of_lt hp0)],
  suffices h_inv_rpow : ((∫⁻ (c : α), f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = (∫⁻ (c : α), f c ^ p ∂μ)⁻¹,
  by rw h_inv_rpow,
  rw [inv_rpow_of_pos hp0, ←rpow_mul, div_eq_mul_inv, one_mul,
    _root_.inv_mul_cancel (ne_of_lt hp0).symm, rpow_one],
end

lemma lintegral_rpow_fun_mul_inv_snorm_eq_one {p : ℝ} (hp0_lt : 0 < p) {f : α → ennreal}
  (hf : measurable f) (hf_nonzero : ∫⁻ a, (f a)^p ∂μ ≠ 0) (hf_top : ∫⁻ a, (f a)^p ∂μ ≠ ⊤) :
  ∫⁻ c, (fun_mul_inv_snorm f p μ c)^p ∂μ = 1 :=
begin
  simp_rw fun_mul_inv_snorm_rpow hp0_lt,
  rw [lintegral_mul_const _ hf.ennreal_rpow_const, mul_inv_cancel hf_nonzero hf_top],
end

/-- Hölder's inequality in case of finite non-zero integrals -/
lemma lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : ℝ} (hpq : p.is_conjugate_exponent q)
  {f g : α → ennreal} (hf : measurable f) (hg : measurable g)
  (hf_nontop : ∫⁻ a, (f a)^p ∂μ ≠ ⊤) (hg_nontop : ∫⁻ a, (g a)^q ∂μ ≠ ⊤)
  (hf_nonzero : ∫⁻ a, (f a)^p ∂μ ≠ 0) (hg_nonzero : ∫⁻ a, (g a)^q ∂μ ≠ 0) :
  ∫⁻ a, (f * g) a ∂μ ≤ (∫⁻ a, (f a)^p ∂μ)^(1/p) * (∫⁻ a, (g a)^q ∂μ)^(1/q) :=
begin
  let npf := (∫⁻ (c : α), (f c) ^ p ∂μ) ^ (1/p),
  let nqg := (∫⁻ (c : α), (g c) ^ q ∂μ) ^ (1/q),
  calc ∫⁻ (a : α), (f * g) a ∂μ
    = ∫⁻ (a : α), ((fun_mul_inv_snorm f p μ * fun_mul_inv_snorm g q μ) a)
      * (npf * nqg) ∂μ :
  begin
    refine lintegral_congr (λ a, _),
    rw [pi.mul_apply, fun_eq_fun_mul_inv_snorm_mul_snorm f hf_nonzero hf_nontop,
      fun_eq_fun_mul_inv_snorm_mul_snorm g hg_nonzero hg_nontop, pi.mul_apply],
    ring,
  end
  ... ≤ npf * nqg :
  begin
    rw lintegral_mul_const' (npf * nqg) _ (by simp [hf_nontop, hg_nontop, hf_nonzero, hg_nonzero]),
    nth_rewrite 1 ←one_mul (npf * nqg),
    refine mul_le_mul _ (le_refl (npf * nqg)),
    have hf1 := lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.pos hf hf_nonzero hf_nontop,
    have hg1 := lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.symm.pos hg hg_nonzero hg_nontop,
    exact lintegral_mul_le_one_of_lintegral_rpow_eq_one hpq (hf.ennreal_mul measurable_const)
      (hg.ennreal_mul measurable_const) hf1 hg1,
  end
end

lemma ae_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0_lt : 0 < p) {f : α → ennreal}
  (hf : measurable f) (hf_zero : ∫⁻ a, (f a)^p ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  rw lintegral_eq_zero_iff hf.ennreal_rpow_const at hf_zero,
  refine filter.eventually.mp hf_zero (filter.eventually_of_forall (λ x, _)),
  dsimp only,
  rw [pi.zero_apply, rpow_eq_zero_iff],
  intro hx,
  cases hx,
  { exact hx.left, },
  { exfalso,
    linarith, },
end

lemma lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0_lt : 0 < p)
  {f g : α → ennreal} (hf : measurable f) (hf_zero : ∫⁻ a, (f a)^p ∂μ = 0) :
  ∫⁻ a, (f * g) a ∂μ = 0 :=
begin
  rw ←@lintegral_zero_fun α _ μ,
  refine lintegral_congr_ae _,
  suffices h_mul_zero : f * g =ᵐ[μ] 0 * g , by rwa zero_mul at h_mul_zero,
  have hf_eq_zero : f =ᵐ[μ] 0, from ae_eq_zero_of_lintegral_rpow_eq_zero hp0_lt hf hf_zero,
  exact filter.eventually_eq.mul hf_eq_zero (ae_eq_refl g),
end

lemma lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : ℝ} (hp0_lt : 0 < p) (hq0 : 0 ≤ q)
  {f g : α → ennreal} (hf_top : ∫⁻ a, (f a)^p ∂μ = ⊤) (hg_nonzero : ∫⁻ a, (g a)^q ∂μ ≠ 0) :
  ∫⁻ a, (f * g) a ∂μ ≤ (∫⁻ a, (f a)^p ∂μ) ^ (1/p) * (∫⁻ a, (g a)^q ∂μ) ^ (1/q) :=
begin
  refine le_trans le_top (le_of_eq _),
  have hp0_inv_lt : 0 < 1/p, by simp [hp0_lt],
  rw [hf_top, ennreal.top_rpow_of_pos hp0_inv_lt],
  simp [hq0, hg_nonzero],
end

/-- Hölder's inequality for functions `α → ennreal`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem lintegral_mul_le_Lp_mul_Lq (μ : measure α) {p q : ℝ} (hpq : p.is_conjugate_exponent q)
  {f g : α → ennreal} (hf : measurable f) (hg : measurable g) :
  ∫⁻ a, (f * g) a ∂μ ≤ (∫⁻ a, (f a)^p ∂μ) ^ (1/p) * (∫⁻ a, (g a)^q ∂μ) ^ (1/q) :=
begin
  by_cases hf_zero : ∫⁻ a, (f a) ^ p ∂μ = 0,
  { refine le_trans (le_of_eq _) (zero_le _),
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.pos hf hf_zero, },
  by_cases hg_zero : ∫⁻ a, (g a) ^ q ∂μ = 0,
  { refine le_trans (le_of_eq _) (zero_le _),
    rw mul_comm,
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.symm.pos hg hg_zero, },
  by_cases hf_top : ∫⁻ a, (f a) ^ p ∂μ = ⊤,
  { exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.pos hpq.symm.nonneg hf_top hg_zero, },
  by_cases hg_top : ∫⁻ a, (g a) ^ q ∂μ = ⊤,
  { rw [mul_comm, mul_comm ((∫⁻ (a : α), (f a) ^ p ∂μ) ^ (1 / p))],
    exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.symm.pos hpq.nonneg hg_top hf_zero, },
  -- non-⊤ non-zero case
  exact ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top hpq hf hg hf_top hg_top hf_zero
    hg_zero,
end

end ennreal

/-- Hölder's inequality for functions `α → nnreal`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem nnreal.lintegral_mul_le_Lp_mul_Lq {p q : ℝ} (hpq : p.is_conjugate_exponent q)
  {f g : α → nnreal} (hf : measurable f) (hg : measurable g) :
  ∫⁻ a, (f * g) a ∂μ ≤ (∫⁻ a, (f a)^p ∂μ)^(1/p) * (∫⁻ a, (g a)^q ∂μ)^(1/q) :=
begin
  simp_rw [pi.mul_apply, ennreal.coe_mul],
  exact ennreal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.ennreal_coe hg.ennreal_coe,
end

end lintegral
