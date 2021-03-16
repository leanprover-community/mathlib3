/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.asymptotics.asymptotic_equivalent
import analysis.asymptotics.specific_asymptotics
import data.polynomial.erase_lead

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rationals functions.
The main result is `eval_is_equivalent_at_top_eval_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/

open filter finset asymptotics
open_locale asymptotics topological_space

namespace polynomial

variables {𝕜 : Type*} [normed_linear_ordered_field 𝕜] (P Q : polynomial 𝕜)

lemma eventually_no_roots (hP : P ≠ 0) : ∀ᶠ x in filter.at_top, ¬ P.is_root x :=
begin
  obtain ⟨x₀, hx₀⟩ := polynomial.exists_max_root P hP,
  refine filter.eventually_at_top.mpr (⟨x₀ + 1, λ x hx h, _⟩),
  exact absurd (hx₀ x h) (not_le.mpr (lt_of_lt_of_le (lt_add_one x₀) hx)),
end

variables [order_topology 𝕜]

lemma is_equivalent_at_top_lead :
  (λ x, eval x P) ~[at_top] (λ x, P.leading_coeff * x ^ P.nat_degree) :=
begin
  by_cases h : P = 0,
  { simp [h] },
  { conv_lhs
    { funext,
      rw [polynomial.eval_eq_finset_sum, sum_range_succ, add_comm] },
    exact is_equivalent.refl.add_is_o (is_o.sum $ λ i hi, is_o.const_mul_left
      (is_o.const_mul_right (λ hz, h $ leading_coeff_eq_zero.mp hz) $
        is_o_pow_pow_at_top_of_lt (mem_range.mp hi)) _) }
end

lemma tendsto_at_top_of_leading_coeff_nonneg (hdeg : 1 ≤ P.degree) (hnng : 0 ≤ P.leading_coeff) :
  tendsto (λ x, eval x P) at_top at_top :=
P.is_equivalent_at_top_lead.symm.tendsto_at_top
  (tendsto_const_mul_pow_at_top (le_nat_degree_of_coe_le_degree hdeg)
    (lt_of_le_of_ne hnng $ ne.symm $ mt leading_coeff_eq_zero.mp $ ne_zero_of_coe_le_degree hdeg))

lemma tendsto_at_bot_of_leading_coeff_nonpos (hdeg : 1 ≤ P.degree) (hnps : P.leading_coeff ≤ 0) :
  tendsto (λ x, eval x P) at_top at_bot :=
P.is_equivalent_at_top_lead.symm.tendsto_at_bot
  (tendsto_neg_const_mul_pow_at_top (le_nat_degree_of_coe_le_degree hdeg)
    (lt_of_le_of_ne hnps $ mt leading_coeff_eq_zero.mp $ ne_zero_of_coe_le_degree hdeg))

lemma abs_tendsto_at_top (hdeg : 1 ≤ P.degree) :
  tendsto (λ x, abs $ eval x P) at_top at_top :=
begin
  by_cases hP : 0 ≤ P.leading_coeff,
  { exact tendsto_abs_at_top_at_top.comp (P.tendsto_at_top_of_leading_coeff_nonneg hdeg hP)},
  { push_neg at hP,
    exact tendsto_abs_at_bot_at_top.comp (P.tendsto_at_bot_of_leading_coeff_nonpos hdeg hP.le)}
end

lemma is_equivalent_at_top_div :
  (λ x, (eval x P)/(eval x Q)) ~[at_top]
    λ x, P.leading_coeff/Q.leading_coeff * x^(P.nat_degree - Q.nat_degree : ℤ) :=
begin
  by_cases hP : P = 0,
  { simp [hP] },
  by_cases hQ : Q = 0,
  { simp [hQ] },
  refine (P.is_equivalent_at_top_lead.symm.div
          Q.is_equivalent_at_top_lead.symm).symm.trans
         (eventually_eq.is_equivalent ((eventually_gt_at_top 0).mono $ λ x hx, _)),
  simp [← div_mul_div, hP, hQ, fpow_sub hx.ne.symm]
end

lemma div_tendsto_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top (𝓝 0) :=
begin
  by_cases hP : P = 0,
  { simp [hP, tendsto_const_nhds] },
  rw ←  nat_degree_lt_nat_degree_iff hP at hdeg,
  refine (is_equivalent_at_top_div P Q).symm.tendsto_nhds _,
  rw ← mul_zero,
  refine (tendsto_fpow_at_top_zero _).const_mul _,
  linarith
end

lemma div_tendsto_leading_coeff_div_of_degree_eq (hdeg : P.degree = Q.degree) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top (𝓝 $ P.leading_coeff / Q.leading_coeff) :=
begin
  refine (is_equivalent_at_top_div P Q).symm.tendsto_nhds _,
  rw show (P.nat_degree : ℤ) = Q.nat_degree, by simp [hdeg, nat_degree],
  simp [tendsto_const_nhds]
end

lemma div_tendsto_at_top_of_degree_gt' (hdeg : Q.degree < P.degree)
  (hpos : 0 < P.leading_coeff/Q.leading_coeff) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_top :=
begin
  have hQ : Q ≠ 0 := λ h, by {simp only [h, div_zero, leading_coeff_zero] at hpos, linarith},
  rw ← nat_degree_lt_nat_degree_iff hQ at hdeg,
  refine (is_equivalent_at_top_div P Q).symm.tendsto_at_top _,
  apply tendsto.const_mul_at_top hpos,
  apply tendsto_fpow_at_top_at_top,
  linarith
end

lemma div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree)
  (hQ : Q ≠ 0) (hnng : 0 ≤ P.leading_coeff/Q.leading_coeff) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_top :=
have ratio_pos : 0 < P.leading_coeff/Q.leading_coeff,
  from lt_of_le_of_ne hnng
    (div_ne_zero (λ h, ne_zero_of_degree_gt hdeg $ leading_coeff_eq_zero.mp h)
      (λ h, hQ $ leading_coeff_eq_zero.mp h)).symm,
div_tendsto_at_top_of_degree_gt' P Q hdeg ratio_pos

lemma div_tendsto_at_bot_of_degree_gt' (hdeg : Q.degree < P.degree)
  (hneg : P.leading_coeff/Q.leading_coeff < 0) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_bot :=
begin
  have hQ : Q ≠ 0 := λ h, by {simp only [h, div_zero, leading_coeff_zero] at hneg, linarith},
  rw ← nat_degree_lt_nat_degree_iff hQ at hdeg,
  refine (is_equivalent_at_top_div P Q).symm.tendsto_at_bot _,
  apply tendsto.neg_const_mul_at_top hneg,
  apply tendsto_fpow_at_top_at_top,
  linarith
end

lemma div_tendsto_at_bot_of_degree_gt (hdeg : Q.degree < P.degree)
  (hQ : Q ≠ 0) (hnps : P.leading_coeff/Q.leading_coeff ≤ 0) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_bot :=
have ratio_neg : P.leading_coeff/Q.leading_coeff < 0,
  from lt_of_le_of_ne hnps
    (div_ne_zero (λ h, ne_zero_of_degree_gt hdeg $ leading_coeff_eq_zero.mp h)
      (λ h, hQ $ leading_coeff_eq_zero.mp h)),
div_tendsto_at_bot_of_degree_gt' P Q hdeg ratio_neg

lemma eval_div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree)
  (hQ : Q ≠ 0) :
  tendsto (λ x, abs ((eval x P)/(eval x Q))) at_top at_top :=
begin
  by_cases h : 0 ≤ P.leading_coeff/Q.leading_coeff,
  { exact tendsto_abs_at_top_at_top.comp (P.div_tendsto_at_top_of_degree_gt Q hdeg hQ h) },
  { push_neg at h,
    exact tendsto_abs_at_bot_at_top.comp (P.div_tendsto_at_bot_of_degree_gt Q hdeg hQ h.le) }
end

theorem is_O_of_degree_le (h : P.degree ≤ Q.degree) :
  is_O (λ x, eval x P) (λ x, eval x Q) filter.at_top :=
begin
  by_cases hp : P = 0,
  { simpa [hp] using is_O_zero (λ x, eval x Q) filter.at_top },
  { have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp,
    cases le_iff_lt_or_eq.mp h with h h,
    { have := polynomial.div_tendsto_zero_of_degree_lt P Q h,
      refine is_O_at_top_of_div_tends_to_finite _ 0 this,
      refine filter.mem_sets_of_superset (polynomial.eventually_no_roots Q hq) _,
      exact λ x hx hx', absurd hx' hx },
    { have := polynomial.div_tendsto_leading_coeff_div_of_degree_eq P Q h,
      refine is_O_at_top_of_div_tends_to_finite _ _ this,
      refine filter.mem_sets_of_superset (polynomial.eventually_no_roots Q hq) _,
      exact λ x hx hx', absurd hx' hx } }
end

end polynomial
