/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.covering.vitali
import measure_theory.covering.differentiation

/-!
# Lebesgue's density theorem

In this file we combine general results about existence of Vitali families for doubling measures
with results about differentiation along a Vitali family to obtain an explicit form of Lebesgue's
density theorem.

## Main results

  * `closed_ball.ae_tendsto_measure_inter_div`: a version of Lebesgue's density theorem for
  sequences of balls converging on a point but whose centres are not required to be fixed.

-/

open set filter metric measure_theory
open_locale nnreal topological_space

variables {α : Type*} [metric_space α] [proper_space α]
variables [measurable_space α] {μ : measure α} [borel_space α] [is_locally_finite_measure μ]

/-- A version of *Lebesgue's density theorem* for a sequence of closed balls whose centres are
not required to be fixed.

See also `besicovitch.ae_tendsto_measure_inter_div`. -/
lemma closed_ball.ae_tendsto_measure_inter_div (C : ℝ≥0)
  (h : ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (2 * ε)) ≤ C * μ (closed_ball x ε)) (S : set α) :
  ∀ᵐ x ∂μ.restrict S, ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ)
    (δlim : tendsto δ l (𝓝[>] 0))
    (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (δ j)),
    tendsto (λ j, μ (S ∩ closed_ball (w j) (δ j)) / μ (closed_ball (w j) (δ j))) l (𝓝 1) :=
begin
  replace h : ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 8),
    ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (t * ε)) ≤ ↑(C^3) * μ (closed_ball x ε),
  { intros t ht,
    let hp : 0 < (2 : ℝ) := two_pos,
    apply ((eventually_nhds_within_pos_mul_left hp $ eventually_nhds_within_pos_mul_left hp h).and $
      (eventually_nhds_within_pos_mul_left hp h).and h).mono,
    rintros ε ⟨h₁, h₂, h₃⟩ x,
    calc μ (closed_ball x (t * ε))
          ≤ μ (closed_ball x (8 * ε)) : measure_mono _
      ... = μ (closed_ball x (2 * (2 * (2 * ε)))) : by { simp only [← mul_assoc], norm_num, }
      ... ≤ C * μ (closed_ball x (2 * (2 * ε))) : h₁ x
      ... ≤ C * (C * μ (closed_ball x (2 * ε))) : ennreal.mul_left_mono $ h₂ x
      ... ≤ C * (C * (C*μ (closed_ball x ε))) : ennreal.mul_left_mono $ ennreal.mul_left_mono $ h₃ x
      ... = ↑(C^3) * μ (closed_ball x ε) : by simp only [← mul_assoc, ← pow_three, ennreal.coe_pow],
    { cases le_or_gt 0 ε with hε hε,
      { exact closed_ball_subset_closed_ball (mul_le_mul_of_nonneg_right ht.2 hε), },
      { rw [closed_ball_eq_empty.mpr (mul_neg_of_pos_of_neg ht.1 hε),
            closed_ball_eq_empty.mpr (by linarith : 8 * ε < 0)], }, }, },
  let v : vitali_family μ := vitali.vitali_family μ (C^3) (λ x ε hε, by
  { replace h := forall_eventually_of_eventually_forall (h 6 $ by norm_num),
    simpa only [exists_prop] using
      ((eventually_nhds_within_pos_mem_Ioc hε).and (h x)).frequently.exists, }),
  filter_upwards [v.ae_tendsto_measure_inter_div S] with x hx ι l w δ δlim xmem,
  have : tendsto (λ j, closed_ball (w j) (δ j)) l (v.filter_at x),
  { refine v.tendsto_filter_at_iff.mpr ⟨_, (λ ε hε, _)⟩,
    { simp only [v, vitali.vitali_family],
      have δpos : ∀ᶠ j in l, 0 < δ j := eventually_mem_of_tendsto_nhds_within δlim,
      apply ((δlim.eventually (h 7 $ by norm_num)).and (xmem.and δpos)).mono,
      rintros j ⟨hjC, hjx, hjδ⟩,
      have hdiam : 3 * diam (closed_ball (w j) (δ j)) ≤ 6 * δ j,
      { linarith [@diam_closed_ball _ _ (w j) _ hjδ.le], },
      refine ⟨hjx, is_closed_ball, (nonempty_ball.mpr hjδ).mono ball_subset_interior_closed_ball,
        (measure_mono (closed_ball_subset_closed_ball hdiam)).trans _⟩,
      suffices : closed_ball x (6 * δ j) ⊆ closed_ball (w j) (7 * δ j),
      { exact (measure_mono this).trans ((hjC _).trans (le_refl _)), },
      intros y hy,
      simp only [mem_closed_ball] at hjx hy ⊢,
      rw dist_comm at hjx,
      linarith [dist_triangle_right y (w j) x], },
    { have δpos := eventually_mem_of_tendsto_nhds_within δlim,
      replace δlim := tendsto_nhds_of_tendsto_nhds_within δlim,
      apply (((metric.tendsto_nhds.mp δlim _ (half_pos hε)).and δpos).and xmem).mono,
      rintros j ⟨hj, hx⟩ y hy,
      replace hj : δ j < ε / 2 := by simpa [abs_eq_self.mpr (mem_Ioi.mp hj.2).le] using hj.1,
      simp only [mem_closed_ball] at hx hy ⊢,
      linarith [dist_triangle_right y x (w j)], } },
  exact hx.comp this,
end
