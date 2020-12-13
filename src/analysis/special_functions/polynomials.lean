/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.asymptotic_equivalent
import data.polynomial.erase_lead

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rationals functions.
The main result is `eval_is_equivalent_at_top_eval_lead`, which states that for
any polynomial `P` of degree `n` with leading coeff `a`, the corresponding polynomial
function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coeffs of the considered polynomials.
-/

open filter finset asymptotics
open_locale asymptotics topological_space

namespace polynomial

variable {α : Type*}

lemma eval_is_equivalent_at_top_eval_lead
  [normed_linear_ordered_field α] [order_topology α] (P : polynomial α) :
  (λ x, eval x P) ~[at_top] (λ x, P.leading_coeff * x ^ P.nat_degree) :=
begin
  by_cases h : P = 0,
  { simp [h] },
  { conv
    { congr,
      funext,
      rw [polynomial.eval_eq_finset_sum, sum_range_succ, add_comm] },
    exact is_equivalent.refl.add_is_o (is_o.sum $ λ i hi, is_o.const_mul_left
      (is_o.const_mul_right (λ hz, h $ leading_coeff_eq_zero.mp hz) $
        is_o_pow_pow_at_top_of_lt (mem_range.mp hi)) _) }
end

lemma eval_tendsto_at_top_of_leading_coeff_nonneg [normed_linear_ordered_field α] (P : polynomial α)
  [order_topology α] (hdeg : 1 ≤ P.degree) (hnng : 0 ≤ P.leading_coeff) :
  tendsto (λ x, eval x P) at_top at_top :=
begin
  have hP : P ≠ 0,
  { rw ← degree_nonneg_iff_ne_zero, refine trans (by exact_mod_cast zero_le_one) hdeg },
  rw degree_eq_nat_degree hP at hdeg,
  exact P.eval_is_equivalent_at_top_eval_lead.symm.tendsto_at_top
    (tendsto_at_top_mul_left' (lt_of_le_of_ne hnng $ λ h, hP $ leading_coeff_eq_zero.mp h.symm)
      (tendsto_pow_at_top $ by exact_mod_cast hdeg))
end

lemma eval_tendsto_at_bot_of_leading_coeff_nonpos [normed_linear_ordered_field α] (P : polynomial α)
  [order_topology α] (hdeg : 1 ≤ P.degree) (hnps : P.leading_coeff ≤ 0) :
  tendsto (λ x, eval x P) at_top at_bot :=
begin
  have hP : P ≠ 0,
  { rw ← degree_nonneg_iff_ne_zero, refine trans (by exact_mod_cast zero_le_one) hdeg },
  rw degree_eq_nat_degree hP at hdeg,
  exact P.eval_is_equivalent_at_top_eval_lead.symm.tendsto_at_bot
    (tendsto_at_bot_mul_left' (lt_of_le_of_ne hnps $ λ h, hP $ leading_coeff_eq_zero.mp h)
      (tendsto_pow_at_top $ by exact_mod_cast hdeg)),
end

lemma abs_eval_tendsto_at_top [normed_linear_ordered_field α] (P : polynomial α)
  [order_topology α] (hdeg : 1 ≤ P.degree) :
  tendsto (λ x, abs $ eval x P) at_top at_top :=
begin
  by_cases hP : 0 ≤ P.leading_coeff,
  { exact tendsto_abs_at_top_at_top.comp (P.eval_tendsto_at_top_of_leading_coeff_nonneg hdeg hP)},
  { push_neg at hP,
    exact tendsto_abs_at_bot_at_top.comp (P.eval_tendsto_at_bot_of_leading_coeff_nonpos hdeg hP.le)}
end

lemma eval_div_tendsto_zero_of_degree_lt [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : P.degree < Q.degree) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top (𝓝 0) :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_nhds _,
  conv
  { congr,
    funext,
    rw ← div_mul_div },
  by_cases hPQ : P = 0 ∨ Q = 0,
  { rcases hPQ with hP | hQ,
    { simp [hP, tendsto_const_nhds] },
    { simp [hQ, tendsto_const_nhds] } },
  { push_neg at hPQ,
    rw ← mul_zero _,
    rw [degree_eq_nat_degree hPQ.1, degree_eq_nat_degree hPQ.2] at hdeg,
    refine tendsto.const_mul _ (tendsto_pow_div_pow_at_top_of_lt _),
    exact_mod_cast hdeg }
end

lemma eval_div_tendsto_leading_coeff_div_of_degree_eq [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : P.degree = Q.degree) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top (𝓝 $ P.leading_coeff / Q.leading_coeff) :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_nhds _,
  conv
  { congr,
    funext,
    rw ← div_mul_div,
    rw nat_degree_eq_of_degree_eq hdeg,
    skip, skip,
    rw ← mul_one (P.leading_coeff / Q.leading_coeff) },
  exact tendsto.const_mul _ (tendsto_const_nhds.congr' $ (eventually_gt_at_top 0).mono $
    λ x (hx : 0 < x), (div_self (pow_pos hx Q.nat_degree).ne.symm).symm),
end

lemma eval_div_tendsto_at_top_of_degree_gt [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : Q.degree < P.degree)
  (hQ : Q ≠ 0) (hnng : 0 ≤ P.leading_coeff/Q.leading_coeff) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_top :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_at_top _,
  conv
  { congr,
    funext,
    rw ← div_mul_div },
  have hP : P ≠ 0,
  { rw ← degree_nonneg_iff_ne_zero at ⊢ hQ, exact hQ.trans hdeg.le },
  have ratio_pos : 0 < P.leading_coeff/Q.leading_coeff :=
    lt_of_le_of_ne hnng (div_ne_zero (λ h, hP $ leading_coeff_eq_zero.mp h)
      (λ h, hQ $ leading_coeff_eq_zero.mp h)).symm,
  rw [degree_eq_nat_degree hP, degree_eq_nat_degree hQ] at hdeg,
  norm_cast at hdeg,
  have one_le_nat_degree_sub : 1 ≤ P.nat_degree - Q.nat_degree :=
    (nat.le_sub_left_iff_add_le hdeg.le).mpr (nat.lt_iff_add_one_le.mp hdeg),
  exact tendsto_at_top_mul_left' ratio_pos ((tendsto_pow_at_top one_le_nat_degree_sub).congr' $
    (eventually_gt_at_top 0).mono $ λ x hx, pow_sub' x hx.ne.symm hdeg.le)
end

lemma eval_div_tendsto_at_bot_of_degree_gt [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : Q.degree < P.degree)
  (hQ : Q ≠ 0) (hnng : P.leading_coeff/Q.leading_coeff ≤ 0) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_bot :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_at_bot _,
  conv
  { congr,
    funext,
    rw ← div_mul_div },
  have hP : P ≠ 0,
  { rw ← degree_nonneg_iff_ne_zero at ⊢ hQ, exact hQ.trans hdeg.le },
  have ratio_neg : P.leading_coeff/Q.leading_coeff < 0 :=
    lt_of_le_of_ne hnng (div_ne_zero (λ h, hP $ leading_coeff_eq_zero.mp h)
      (λ h, hQ $ leading_coeff_eq_zero.mp h)),
  rw [degree_eq_nat_degree hP, degree_eq_nat_degree hQ] at hdeg,
  norm_cast at hdeg,
  have one_le_nat_degree_sub : 1 ≤ P.nat_degree - Q.nat_degree :=
    (nat.le_sub_left_iff_add_le hdeg.le).mpr (nat.lt_iff_add_one_le.mp hdeg),
  exact tendsto_at_bot_mul_left' ratio_neg ((tendsto_pow_at_top one_le_nat_degree_sub).congr' $
    (eventually_gt_at_top 0).mono $ λ x hx, pow_sub' x hx.ne.symm hdeg.le)
end

lemma abs_eval_div_tendsto_at_top_of_degree_gt [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : Q.degree < P.degree)
  (hQ : Q ≠ 0) :
  tendsto (λ x, abs ((eval x P)/(eval x Q))) at_top at_top :=
begin
  by_cases h : 0 ≤ P.leading_coeff/Q.leading_coeff,
  { exact tendsto_abs_at_top_at_top.comp (P.eval_div_tendsto_at_top_of_degree_gt Q hdeg hQ h) },
  { push_neg at h,
    exact tendsto_abs_at_bot_at_top.comp (P.eval_div_tendsto_at_bot_of_degree_gt Q hdeg hQ h.le) }
end

end polynomial
