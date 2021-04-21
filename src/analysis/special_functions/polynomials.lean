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

lemma leading_coeff_nonneg_of_tendsto_at_top
  (h : tendsto (λ x, eval x P) at_top at_top) :
  1 ≤ P.degree ∧ 0 ≤ P.leading_coeff :=
begin
  have : tendsto (λ x, P.leading_coeff * x ^ P.nat_degree) at_top at_top := begin
    sorry,
  end,
  rw tendsto_const_mul_pow_at_top_iff P.leading_coeff P.nat_degree at this,
  exact this,
end

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

lemma abs_div_tendsto_at_top_of_degree_gt (hdeg : Q.degree < P.degree)
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
    have hPQ : ∀ᶠ (x : 𝕜) in at_top, eval x Q = 0 → eval x P = 0 :=
      filter.mem_sets_of_superset (polynomial.eventually_no_roots Q hq) (λ x h h', absurd h' h),
    cases le_iff_lt_or_eq.mp h with h h,
    { exact is_O_of_div_tendsto_nhds hPQ 0 (div_tendsto_zero_of_degree_lt P Q h) },
    { exact is_O_of_div_tendsto_nhds hPQ _ (div_tendsto_leading_coeff_div_of_degree_eq P Q h) } }
end

-- lemma le_of_is_O_pow {a b : ℕ}
--   (h : is_O (λ (x : 𝕜), x ^ a) (λ (x : 𝕜), x ^ b) filter.at_top) :
--   a ≤ b :=
-- begin
--   rw is_O_iff_div_is_bounded_under sorry at h,
--   obtain ⟨x, hx⟩ := h,
--   -- unfold filter.eventually at hx,
--   simp only [filter.eventually, filter.mem_map, ge_iff_le, set.mem_set_of_eq] at hx,
--   rw mem_at_top_sets at hx,
--   obtain ⟨k, hk⟩ := hx,
--   specialize hk k le_rfl,
--   simp [← div_pow] at hk,

-- end

-- lemma eq_zero_iff : P = 0 ↔ (λ x, eval x P) = 0 :=
-- begin
--   refine ⟨λ h, _, λ h, _⟩,
--   {
--     refine function.funext_iff.mpr (λ x, _),
--     rw [h, eval_zero, pi.zero_apply],
--   },
--   {
--     refine funext (λ x, _),
--     sorry,
--   }
-- end

lemma is_O_zero_iff_is_eventually_zero {α β : Type*} [normed_group β]
  {u : α → β} {l : filter α} :
  is_O u (0 : α → β) l ↔ u ~[l] 0 :=
begin
  refine ⟨_, _⟩,
  {
    refine λ h, _,
    erw is_O_zero_right_iff at h,
    rw is_equivalent_zero_iff_eventually_zero,
    rw eventually_eq_iff_exists_mem,
    refine ⟨{x : α | u x = 0}, h, λ x hx, hx⟩,
  },
  {
    exact is_equivalent.is_O,
  }
end

lemma eq_zero_of_is_O_zero (h : is_O (λ (x : 𝕜), eval x P) (0 : 𝕜 → 𝕜) filter.at_top) :
  P = 0 :=
begin
  have : (λ x, eval x P) ~[at_top] 0 := begin
    refine is_O_zero_iff_is_eventually_zero.mp h,
  end,
  have hP := is_equivalent_at_top_lead P,
  have := is_equivalent.trans hP.symm this,
  have : P.leading_coeff = 0 := begin
    sorry,
  end,
  refine leading_coeff_eq_zero.mp this,
end

lemma norm_ge_mem_at_top {b : ℝ} :
  {x : 𝕜 | ∥x∥ > b} ∈ (filter.at_top : filter 𝕜) :=
begin
  -- rw filter.mem_at_top_sets,
  have : ∃ (n : ℕ), b < ↑n := sorry,
  obtain ⟨n, hn⟩ := this,
  have : b ≤ ∥(n : 𝕜)∥ := begin
    sorry,
  end,
  refine at_top.sets_of_superset (Ioi_mem_at_top (n : 𝕜)) (λ x hx, _),
  refine lt_of_le_of_lt this _,
  simp at hx ⊢, sorry,
end

theorem degree_eq_of_is_O_of_is_O
  (hPQ : is_O (λ x, eval x P) (λ x, eval x Q) filter.at_top)
  (hQP : is_O (λ x, eval x Q) (λ x, eval x P) filter.at_top) :
  P.degree = Q.degree :=
begin
  by_cases h0 : P = 0 ∨ Q = 0,
  { cases h0 with hP hQ,
    { sorry },
    { sorry } },

  rw is_O_iff_div_is_bounded_under sorry at hPQ hQP,

    -- have hPQ := div_tendsto_at_top_of_degree_gt P Q hc hQ sorry,
    -- replace hPQ := is_equivalent.tendsto_at_top (is_equivalent_at_top_div P Q) hPQ,

    -- have hnorm : tendsto (λ (x : 𝕜), ∥x∥) at_top at_top := begin
    --   have := (continuous_norm : continuous (λ (x : 𝕜), ∥x∥)),
    --   have := normed_field,
    --   rw tendsto_at_top,
    -- end,
    -- replace := tendsto.comp hnorm this,

    -- rw is_O_iff_div_is_bounded_under sorry at h,
    -- obtain ⟨b, hb⟩ := h,
    -- unfold filter.eventually at hb,
    -- simp only [filter.mem_map, ge_iff_le, set.mem_set_of_eq] at hb,

    -- rw tendsto_at_top at this,
    -- have : ∃ (x : 𝕜), ∥eval x P / eval x Q∥ = b := sorry,
    -- have := (continuous_norm : continuous (λ (x : 𝕜), ∥x∥)),

end

theorem degree_le_of_is_O'' (h : is_O (λ x, eval x P) (λ x, eval x Q) filter.at_top) :
  P.degree ≤ Q.degree :=
begin
  have := is_O.bound h,
  rw is_O_iff_div_is_bounded_under sorry at h,
  have := is_equivalent_at_top_div P Q,

end

theorem degree_le_of_is_O' (h : is_O (λ x, eval x P) (λ x, eval x Q) filter.at_top) :
  P.degree ≤ Q.degree :=
begin
  by_cases hQ : Q = 0,
  {
    simp only [hQ, degree_eq_bot, degree_zero, le_bot_iff],
    simp only [hQ, eval_zero] at h,
    refine eq_zero_of_is_O_zero P h,
  },
  {
    by_contradiction hc,
    rw not_le at hc,

    suffices : is_O (λ x, eval x Q) (λ x, eval x P) filter.at_top,
    by refine absurd (degree_eq_of_is_O_of_is_O Q P this h) (ne_of_lt hc),

    refine is_O_of_degree_le Q P (le_of_lt hc),
  }
end

theorem degree_le_of_is_O (h : is_O (λ x, eval x P) (λ x, eval x Q) filter.at_top) :
  P.degree ≤ Q.degree :=
begin


  by_cases hPQ : P = 0 ∨ Q = 0,
  {
    cases hPQ with hP hQ,
    {
      simp [hP],
    },
    {
      simp [hQ, degree_eq_bot],
      simp only [hQ, eval_zero] at h,
      refine eq_zero_of_is_O_zero P h,
    }
  },
  rw not_or_distrib at hPQ,
  have hP := is_equivalent_at_top_lead P,
  have hQ := is_equivalent_at_top_lead Q,
  have this := is_O.trans (hP.symm.is_O) h,
  replace this := is_O.trans this hQ.is_O,
  suffices : P.nat_degree ≤ Q.nat_degree,
  by {
    rw degree_eq_nat_degree hPQ.1,
    rw degree_eq_nat_degree hPQ.2,
    refine with_bot.coe_le_coe.mpr this,
  },
  have hP' := is_O_self_const_mul' (is_unit_iff_ne_zero.mpr (leading_coeff_ne_zero.mpr hPQ.1))
    (λ x, x ^ P.nat_degree) filter.at_top,
  have hQ' := is_O_self_const_mul' (begin
    refine is_unit_iff_ne_zero.mpr _,
    refine inv_ne_zero _,
    refine leading_coeff_ne_zero.mpr _,
    refine hPQ.2,
  end : is_unit Q.leading_coeff⁻¹)
    (λ x, Q.leading_coeff * x ^ Q.nat_degree) filter.at_top,
  replace this := is_O.trans hP' this,
  replace this := is_O.trans this hQ',
  clear hP hQ hP' hQ',
  simp only [← mul_assoc, inv_mul_cancel (leading_coeff_ne_zero.mpr hPQ.2), one_mul] at this,
  exact le_of_is_O_pow this,



end

end polynomial
