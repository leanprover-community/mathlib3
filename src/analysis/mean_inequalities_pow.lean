/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import analysis.convex.specific_functions
import tactic.positivity

/-!
# Mean value inequalities

In this file we prove several mean inequalities for finite sums. Versions for integrals of some of
these inequalities are available in `measure_theory.mean_inequalities`.

## Main theorems: generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`zpow_arith_mean_le_arith_mean_zpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `strict_convex_on` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

universes u v

open finset
open_locale classical big_operators nnreal ennreal
noncomputable theory

variables {ι : Type u} (s : finset ι)

namespace real

theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (n : ℕ) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
(convex_on_pow n).map_sum_le hw hw' hz

theorem pow_arith_mean_le_arith_mean_pow_of_even (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) {n : ℕ} (hn : even n) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
hn.convex_on_pow.map_sum_le hw hw' (λ _ _, trivial)

theorem zpow_arith_mean_le_arith_mean_zpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) (m : ℤ) :
  (∑ i in s, w i * z i) ^ m ≤ ∑ i in s, (w i * z i ^ m) :=
(convex_on_zpow m).map_sum_le hw hw' hz

theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, (w i * z i ^ p) :=
(convex_on_rpow hp).map_sum_le hw hw' hz

theorem arith_mean_le_rpow_mean (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
  ∑ i in s, w i * z i ≤ (∑ i in s, (w i * z i ^ p)) ^ (1 / p) :=
begin
  have : 0 < p := by positivity,
  rw [← rpow_le_rpow_iff _ _ this, ← rpow_mul, one_div_mul_cancel (ne_of_gt this), rpow_one],
  exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp,
  all_goals { apply_rules [sum_nonneg, rpow_nonneg_of_nonneg],
    intros i hi,
    apply_rules [mul_nonneg, rpow_nonneg_of_nonneg, hw i hi, hz i hi] },
end

end real

namespace nnreal

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
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] _ hp,
  { simpa [fin.sum_univ_succ] using h, },
  { simp [hw', fin.sum_univ_succ], },
end

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem arith_mean_le_rpow_mean (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) {p : ℝ}
  (hp : 1 ≤ p) :
  ∑ i in s, w i * z i ≤ (∑ i in s, (w i * z i ^ p)) ^ (1 / p) :=
by exact_mod_cast real.arith_mean_le_rpow_mean s _ _ (λ i _, (w i).coe_nonneg)
  (by exact_mod_cast hw') (λ i _, (z i).coe_nonneg) hp

end nnreal

namespace nnreal

private lemma add_rpow_le_one_of_add_le_one {p : ℝ} (a b : ℝ≥0) (hab : a + b ≤ 1)
  (hp1 : 1 ≤ p) :
  a ^ p + b ^ p ≤ 1 :=
begin
  have h_le_one : ∀ x : ℝ≥0, x ≤ 1 → x ^ p ≤ x, from λ x hx, rpow_le_self_of_le_one hx hp1,
  have ha : a ≤ 1, from (self_le_add_right a b).trans hab,
  have hb : b ≤ 1, from (self_le_add_left b a).trans hab,
  exact (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab,
end

lemma add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) :
  a ^ p + b ^ p ≤ (a + b) ^ p :=
begin
  have hp_pos : 0 < p := by positivity,
  by_cases h_zero : a + b = 0,
  { simp [add_eq_zero_iff.mp h_zero, hp_pos.ne'] },
  have h_nonzero : ¬(a = 0 ∧ b = 0), by rwa add_eq_zero_iff at h_zero,
  have h_add : a/(a+b) + b/(a+b) = 1, by rw [div_add_div_same, div_self h_zero],
  have h := add_rpow_le_one_of_add_le_one (a/(a+b)) (b/(a+b)) h_add.le hp1,
  rw [div_rpow a (a+b), div_rpow b (a+b)] at h,
  have hab_0 : (a + b)^p ≠ 0, by simp [hp_pos, h_nonzero],
  have hab_0' : 0 < (a + b) ^ p := zero_lt_iff.mpr hab_0,
  have h_mul : (a + b)^p * (a ^ p / (a + b) ^ p + b ^ p / (a + b) ^ p) ≤ (a + b)^p,
  { nth_rewrite 3 ←mul_one ((a + b)^p),
    exact (mul_le_mul_left hab_0').mpr h, },
  rwa [div_eq_mul_inv, div_eq_mul_inv, mul_add, mul_comm (a^p), mul_comm (b^p), ←mul_assoc,
    ←mul_assoc, mul_inv_cancel hab_0, one_mul, one_mul] at h_mul,
end

lemma rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) :
  (a ^ p + b ^ p) ^ (1/p) ≤ a + b :=
begin
  rw ←@nnreal.le_rpow_one_div_iff _ _ (1/p) (by simp [lt_of_lt_of_le zero_lt_one hp1]),
  rw one_div_one_div,
  exact add_rpow_le_rpow_add _ _ hp1,
end

theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0) (hp_pos : 0 < p) (hpq : p ≤ q) :
  (a ^ q + b ^ q) ^ (1/q) ≤ (a ^ p + b ^ p) ^ (1/p) :=
begin
  have h_rpow : ∀ a : ℝ≥0, a^q = (a^p)^(q/p),
    from λ a, by rw [←nnreal.rpow_mul, div_eq_inv_mul, ←mul_assoc,
      _root_.mul_inv_cancel hp_pos.ne.symm, one_mul],
  have h_rpow_add_rpow_le_add : ((a^p)^(q/p) + (b^p)^(q/p)) ^ (1/(q/p)) ≤ a^p + b^p,
  { refine rpow_add_rpow_le_add (a^p) (b^p) _,
    rwa one_le_div hp_pos, },
  rw [h_rpow a, h_rpow b, nnreal.le_rpow_one_div_iff hp_pos, ←nnreal.rpow_mul, mul_comm,
    mul_one_div],
  rwa one_div_div at h_rpow_add_rpow_le_add,
end

lemma rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  (a + b) ^ p ≤ a ^ p + b ^ p :=
begin
  rcases hp.eq_or_lt with rfl|hp_pos,
  { simp },
  have h := rpow_add_rpow_le a b hp_pos hp1,
  rw one_div_one at h,
  repeat { rw nnreal.rpow_one at h },
  exact (nnreal.le_rpow_one_div_iff hp_pos).mp h
end

end nnreal

namespace ennreal

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0∞`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0∞) (hw' : ∑ i in s, w i = 1) {p : ℝ}
  (hp : 1 ≤ p) :
  (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, (w i * z i ^ p) :=
begin
  have hp_pos : 0 < p, positivity,
  have hp_nonneg : 0 ≤ p, positivity,
  have hp_not_nonpos : ¬ p ≤ 0, by simp [hp_pos],
  have hp_not_neg : ¬ p < 0, by simp [hp_nonneg],
  have h_top_iff_rpow_top : ∀ (i : ι) (hi : i ∈ s), w i * z i = ⊤ ↔ w i * (z i) ^ p = ⊤,
    by simp [ennreal.mul_eq_top, hp_pos, hp_nonneg, hp_not_nonpos, hp_not_neg],
  refine le_of_top_imp_top_of_to_nnreal_le _ _,
  { -- first, prove `(∑ i in s, w i * z i) ^ p = ⊤ → ∑ i in s, (w i * z i ^ p) = ⊤`
    rw [rpow_eq_top_iff, sum_eq_top_iff, sum_eq_top_iff],
    intro h,
    simp only [and_false, hp_not_neg, false_or] at h,
    rcases h.left with ⟨a, H, ha⟩,
    use [a, H],
    rwa ←h_top_iff_rpow_top a H, },
  { -- second, suppose both `(∑ i in s, w i * z i) ^ p ≠ ⊤` and `∑ i in s, (w i * z i ^ p) ≠ ⊤`,
    -- and prove `((∑ i in s, w i * z i) ^ p).to_nnreal ≤ (∑ i in s, (w i * z i ^ p)).to_nnreal`,
    -- by using `nnreal.rpow_arith_mean_le_arith_mean_rpow`.
    intros h_top_rpow_sum _,
    -- show hypotheses needed to put the `.to_nnreal` inside the sums.
    have h_top : ∀ (a : ι), a ∈ s → w a * z a ≠ ⊤,
    { have h_top_sum : ∑ (i : ι) in s, w i * z i ≠ ⊤,
      { intro h,
        rw [h, top_rpow_of_pos hp_pos] at h_top_rpow_sum,
        exact h_top_rpow_sum rfl, },
      exact λ a ha, (lt_top_of_sum_ne_top h_top_sum ha).ne },
    have h_top_rpow : ∀ (a : ι), a ∈ s → w a * z a ^ p ≠ ⊤,
    { intros i hi,
      specialize h_top i hi,
      rwa [ne.def, ←h_top_iff_rpow_top i hi], },
    -- put the `.to_nnreal` inside the sums.
    simp_rw [to_nnreal_sum h_top_rpow, ←to_nnreal_rpow, to_nnreal_sum h_top, to_nnreal_mul,
      ←to_nnreal_rpow],
    -- use corresponding nnreal result
    refine nnreal.rpow_arith_mean_le_arith_mean_rpow s (λ i, (w i).to_nnreal) (λ i, (z i).to_nnreal)
      _ hp,
    -- verify the hypothesis `∑ i in s, (w i).to_nnreal = 1`, using `∑ i in s, w i = 1` .
    have h_sum_nnreal : (∑ i in s, w i) = ↑(∑ i in s, (w i).to_nnreal),
    { rw coe_finset_sum,
      refine sum_congr rfl (λ i hi, (coe_to_nnreal _).symm),
      refine (lt_top_of_sum_ne_top _ hi).ne,
      exact hw'.symm ▸ ennreal.one_ne_top },
    rwa [←coe_eq_coe, ←h_sum_nnreal], },
end

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0∞` and real
exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0∞) (hw' : w₁ + w₂ = 1) {p : ℝ}
  (hp : 1 ≤ p) :
  (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p :=
begin
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] _ hp,
  { simpa [fin.sum_univ_succ] using h, },
  { simp [hw', fin.sum_univ_succ], },
end

end ennreal

namespace ennreal

lemma add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
  a ^ p + b ^ p ≤ (a + b) ^ p :=
begin
  have hp_pos : 0 < p := by positivity,
  by_cases h_top : a + b = ⊤,
  { rw ←@ennreal.rpow_eq_top_iff_of_pos (a + b) p hp_pos at h_top,
    rw h_top,
    exact le_top, },
  obtain ⟨ha_top, hb_top⟩ := add_ne_top.mp h_top,
  lift a to ℝ≥0 using ha_top,
  lift b to ℝ≥0 using hb_top,
  simpa [← ennreal.coe_rpow_of_nonneg _ hp_pos.le] using
    ennreal.coe_le_coe.2 (nnreal.add_rpow_le_rpow_add a b hp1),
end

lemma rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
  (a ^ p + b ^ p) ^ (1/p) ≤ a + b :=
begin
  rw ←@ennreal.le_rpow_one_div_iff _ _ (1/p) (by simp [lt_of_lt_of_le zero_lt_one hp1]),
  rw one_div_one_div,
  exact add_rpow_le_rpow_add _ _ hp1,
end

theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0∞) (hp_pos : 0 < p) (hpq : p ≤ q) :
  (a ^ q + b ^ q) ^ (1/q) ≤ (a ^ p + b ^ p) ^ (1/p) :=
begin
  have h_rpow : ∀ a : ℝ≥0∞, a^q = (a^p)^(q/p),
    from λ a, by rw [← ennreal.rpow_mul, _root_.mul_div_cancel' _ hp_pos.ne'],
  have h_rpow_add_rpow_le_add : ((a^p)^(q/p) + (b^p)^(q/p)) ^ (1/(q/p)) ≤ a^p + b^p,
  { refine rpow_add_rpow_le_add (a^p) (b^p) _,
    rwa one_le_div hp_pos, },
  rw [h_rpow a, h_rpow b, ennreal.le_rpow_one_div_iff hp_pos, ←ennreal.rpow_mul, mul_comm,
    mul_one_div],
  rwa one_div_div at h_rpow_add_rpow_le_add,
end

lemma rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  (a + b) ^ p ≤ a ^ p + b ^ p :=
begin
  rcases hp.eq_or_lt with rfl|hp_pos,
  { suffices : (1 : ℝ≥0∞) ≤ 1 + 1,
    { simpa using this },
    norm_cast,
    norm_num },
  have h := rpow_add_rpow_le a b hp_pos hp1,
  rw one_div_one at h,
  repeat { rw ennreal.rpow_one at h },
  exact (ennreal.le_rpow_one_div_iff hp_pos).mp h,
end

end ennreal
