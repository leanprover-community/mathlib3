/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
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

/-- TODO: Not really sure where this should go -/
lemma helper {x : with_bot ℕ} : 1 ≤ x ↔ 0 < x :=
begin
  refine ⟨λ h, lt_of_lt_of_le (with_bot.coe_lt_coe.mpr zero_lt_one) h, λ h, _⟩,
  cases x,
  { exact false.elim (not_lt_of_lt (with_bot.bot_lt_some 0) h) },
  { rw [← nat.cast_one, with_bot.some_eq_coe x],
    rw [← nat.cast_zero, with_bot.some_eq_coe x] at h,
    exact with_bot.coe_le_coe.mpr (nat.succ_le_iff.mpr (with_bot.coe_lt_coe.mp h)) }
end

variables {𝕜 : Type*} [normed_linear_ordered_field 𝕜] (P Q : polynomial 𝕜)

lemma eventually_no_roots (hP : P ≠ 0) : ∀ᶠ x in filter.at_top, ¬ P.is_root x :=
begin
  obtain ⟨x₀, hx₀⟩ := polynomial.exists_max_root P hP,
  refine filter.eventually_at_top.mpr (⟨x₀ + 1, λ x hx h, _⟩),
  exact absurd (hx₀ x h) (not_le.mpr (lt_of_lt_of_le (lt_add_one x₀) hx)),
end

variables [order_topology 𝕜]

section polynomial_at_top

lemma is_equivalent_at_top_lead :
  (λ x, eval x P) ~[at_top] (λ x, P.leading_coeff * x ^ P.nat_degree) :=
begin
  by_cases h : P = 0,
  { simp [h] },
  { conv_lhs
    { funext,
      rw [polynomial.eval_eq_finset_sum, sum_range_succ] },
    exact is_equivalent.refl.add_is_o (is_o.sum $ λ i hi, is_o.const_mul_left
      (is_o.const_mul_right (λ hz, h $ leading_coeff_eq_zero.mp hz) $
        is_o_pow_pow_at_top_of_lt (mem_range.mp hi)) _) }
end

lemma tendsto_at_top_of_leading_coeff_nonneg (hdeg : 1 ≤ P.degree) (hnng : 0 ≤ P.leading_coeff) :
  tendsto (λ x, eval x P) at_top at_top :=
P.is_equivalent_at_top_lead.symm.tendsto_at_top
  (tendsto_const_mul_pow_at_top (le_nat_degree_of_coe_le_degree hdeg)
    (lt_of_le_of_ne hnng $ ne.symm $ mt leading_coeff_eq_zero.mp $ ne_zero_of_coe_le_degree hdeg))

lemma tendsto_at_top_iff_leading_coeff_nonneg :
  tendsto (λ x, eval x P) at_top at_top ↔ 1 ≤ P.degree ∧ 0 ≤ P.leading_coeff :=
⟨λ h, begin
  have : tendsto (λ x, P.leading_coeff * x ^ P.nat_degree) at_top at_top :=
    is_equivalent.tendsto_at_top (is_equivalent_at_top_lead P) h,
  rw tendsto_const_mul_pow_at_top_iff P.leading_coeff P.nat_degree at this,
  rw [degree_eq_nat_degree (leading_coeff_ne_zero.mp (ne_of_lt this.2).symm), ← nat.cast_one],
  refine ⟨with_bot.coe_le_coe.mpr this.1, le_of_lt this.2⟩,
end, λ h, tendsto_at_top_of_leading_coeff_nonneg P h.1 h.2⟩

lemma tendsto_at_bot_of_leading_coeff_nonpos (hdeg : 1 ≤ P.degree) (hnps : P.leading_coeff ≤ 0) :
  tendsto (λ x, eval x P) at_top at_bot :=
P.is_equivalent_at_top_lead.symm.tendsto_at_bot
  (tendsto_neg_const_mul_pow_at_top (le_nat_degree_of_coe_le_degree hdeg)
    (lt_of_le_of_ne hnps $ mt leading_coeff_eq_zero.mp $ ne_zero_of_coe_le_degree hdeg))

lemma tendsto_at_bot_iff_leading_coeff_nonpos :
  tendsto (λ x, eval x P) at_top at_bot ↔ 1 ≤ P.degree ∧ P.leading_coeff ≤ 0 :=
begin
  refine ⟨λ h, _, λ h, tendsto_at_bot_of_leading_coeff_nonpos P h.1 h.2⟩,
  have : tendsto (λ x, P.leading_coeff * x ^ P.nat_degree) at_top at_bot :=
    (is_equivalent.tendsto_at_bot (is_equivalent_at_top_lead P) h),
  rw tendsto_neg_const_mul_pow_at_top_iff P.leading_coeff P.nat_degree at this,
  rw [degree_eq_nat_degree (leading_coeff_ne_zero.mp (ne_of_lt this.2)), ← nat.cast_one],
  refine ⟨with_bot.coe_le_coe.mpr this.1, le_of_lt this.2⟩,
end

lemma abs_tendsto_at_top (hdeg : 1 ≤ P.degree) :
  tendsto (λ x, abs $ eval x P) at_top at_top :=
begin
  by_cases hP : 0 ≤ P.leading_coeff,
  { exact tendsto_abs_at_top_at_top.comp (P.tendsto_at_top_of_leading_coeff_nonneg hdeg hP)},
  { push_neg at hP,
    exact tendsto_abs_at_bot_at_top.comp (P.tendsto_at_bot_of_leading_coeff_nonpos hdeg hP.le)}
end

lemma abs_is_bounded_under_iff :
  is_bounded_under (≤) at_top (λ x, abs (eval x P)) ↔ P.degree ≤ 0 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { contrapose! h,
    exact not_is_bounded_under_of_tendsto_at_top (abs_tendsto_at_top P (helper.2 h)) },
  { refine ⟨abs (P.coeff 0), eventually_map.mpr (eventually_of_forall (forall_imp (λ _, le_of_eq)
      (λ x, congr_arg abs $ trans (congr_arg (eval x) (eq_C_of_degree_le_zero h)) (eval_C))))⟩ }
end

lemma abs_tendsto_at_top_iff :
  tendsto (λ x, abs $ eval x P) at_top at_top ↔ 1 ≤ P.degree :=
⟨λ h, helper.2 (not_le.mp ((mt (abs_is_bounded_under_iff P).mpr)
  (not_is_bounded_under_of_tendsto_at_top h))), abs_tendsto_at_top P⟩

lemma tendsto_nhds_iff : (∃ c, tendsto (λ x, eval x P) at_top (𝓝 c)) ↔ P.degree ≤ 0 :=
begin
  refine ⟨λ h, _, λ h, (eq_C_of_degree_le_zero h).symm ▸ ⟨P.coeff 0, by simp [tendsto_const_nhds]⟩⟩,
  by_cases hP : P = 0,
  { simp [hP] },
  { obtain ⟨c, h⟩ := h,
    have := is_equivalent.tendsto_nhds (is_equivalent_at_top_lead P) h,
    rw tendsto_const_mul_pow_nhds_iff (leading_coeff_ne_zero.2 hP) at this,
    rw nat_degree_eq_zero_iff_degree_le_zero at this,
    exact this.1 }
end

lemma tendsto_nhds_iff' {c : 𝕜} :
  tendsto (λ x, eval x P) at_top (𝓝 c) ↔ c = P.leading_coeff ∧ P.degree ≤ 0 :=
begin
  refine ⟨λ h, _, λ h, (eq_C_of_degree_le_zero h).symm ▸ ⟨P.coeff 0, by simp [tendsto_const_nhds]⟩⟩,
  by_cases hP : P = 0,
  { simp [hP] },
  { obtain ⟨c, h⟩ := h,
    have := is_equivalent.tendsto_nhds (is_equivalent_at_top_lead P) h,
    rw tendsto_const_mul_pow_nhds_iff (leading_coeff_ne_zero.2 hP) at this,
    rw nat_degree_eq_zero_iff_degree_le_zero at this,
    exact this.1 }
end

end polynomial_at_top

section polynomial_div_at_top

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

lemma div_tendsto_zero_iff_degree_lt (hQ : Q ≠ 0) :
  tendsto (λ x, (eval x P)/(eval x Q)) at_top (𝓝 0) ↔ P.degree < Q.degree :=
begin
  refine ⟨λ h, _, div_tendsto_zero_of_degree_lt P Q⟩,
  have := (is_equivalent_at_top_div P Q).tendsto_nhds h,
  rw tendsto_const_mul_fpow_at_top_zero_iff at this,
  cases this with h h,
  { rw div_eq_zero_iff at h,
    cases h with h h,
    { rw [leading_coeff_eq_zero] at h,
      refine lt_of_le_of_lt (le_of_eq (degree_eq_bot.mpr h)) _,
      refine lt_of_le_of_ne bot_le (ne.symm ((mt (degree_eq_bot.mp)) hQ)) },
    { rw leading_coeff_eq_zero at h,
      refine absurd h hQ } },
  { rw [sub_lt_iff_lt_add, zero_add, int.coe_nat_lt] at h,
    refine degree_lt_degree h }
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

lemma abs_div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree)
  (hQ : Q ≠ 0) :
  tendsto (λ x, abs ((eval x P)/(eval x Q))) at_top at_top :=
begin
  by_cases h : 0 ≤ P.leading_coeff/Q.leading_coeff,
  { exact tendsto_abs_at_top_at_top.comp (P.div_tendsto_at_top_of_degree_gt Q hdeg hQ h) },
  { push_neg at h,
    exact tendsto_abs_at_bot_at_top.comp (P.div_tendsto_at_bot_of_degree_gt Q hdeg hQ h.le) }
end

end polynomial_div_at_top

theorem is_O_of_degree_le (h : P.degree ≤ Q.degree) :
  is_O (λ x, eval x P) (λ x, eval x Q) filter.at_top :=
begin
  by_cases hp : P = 0,
  { simpa [hp] using is_O_zero (λ x, eval x Q) filter.at_top },
  { have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp,
    have hPQ : ∀ᶠ (x : 𝕜) in at_top, eval x Q = 0 → eval x P = 0 :=
      filter.mem_sets_of_superset (polynomial.eventually_no_roots Q hq) (λ x h h', absurd h' h),
    cases le_iff_lt_or_eq.mp h with h h,
    { exact is_O_of_div_tendsto_nhds hPQ 0 (div_tendsto_zero_of_degree_lt P Q h) },
    { exact is_O_of_div_tendsto_nhds hPQ _ (div_tendsto_leading_coeff_div_of_degree_eq P Q h) } }
end

end polynomial
