/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.covering.vitali
import measure_theory.covering.differentiation

/-!
# Doubling measures and Lebesgue's density theorem

A doubling measure `μ` on a metric space is a measure for which there exists a constant `C` such
that for all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

Lebesgue's density theorem states that given a set `S` in a proper metric space with locally-finite
doubling measure `μ` then for almost all points `x` in `S`, for any sequence of closed balls
`B₀, B₁, B₂, ...` containing `x`, the limit `μ (S ∩ Bⱼ) / μ (Bⱼ) → 1` as `j → ∞`.

In this file we combine general results about existence of Vitali families for doubling measures
with results about differentiation along a Vitali family to obtain an explicit form of Lebesgue's
density theorem.

## Main results

  * `is_doubling_measure`: the definition of a doubling measure (as a typeclass).
  * `is_doubling_measure.doubling_constant`: a function yielding the doubling constant `C` appearing
  in the definition of a doubling measure.
  * `is_doubling_measure.ae_tendsto_measure_inter_div`: a version of Lebesgue's density theorem for
  sequences of balls converging on a point but whose centres are not required to be fixed.

-/

noncomputable theory

open set filter metric measure_theory
open_locale nnreal topological_space

/-- A measure `μ` is said to be a doubling measure if there exists a constant `C` such that for
all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius `2 * ε` is
bounded by `C` times the measure of the concentric ball of radius `ε`. -/
class is_doubling_measure {α : Type*} [metric_space α] [measurable_space α] (μ : measure α) :=
(exists_measure_closed_ball_le_mul [] :
  ∃ (C : ℝ≥0), ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (2 * ε)) ≤ C * μ (closed_ball x ε))

namespace is_doubling_measure

variables {α : Type*} [metric_space α] [measurable_space α] (μ : measure α) [is_doubling_measure μ]

/-- The doubling constant of a doubling measure. -/
def doubling_constant : ℝ≥0 := classical.some $ exists_measure_closed_ball_le_mul μ

lemma exists_measure_closed_ball_le_mul' :
  ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (2 * ε)) ≤ (doubling_constant μ) * μ (closed_ball x ε) :=
classical.some_spec $ exists_measure_closed_ball_le_mul μ

lemma exists_measure_closed_ball_le_mul_of_mem_Ioc (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 8) :
  ∀ᶠ ε in 𝓝[>] 0, ∀ x,
    μ (closed_ball x (t * ε)) ≤ ↑((doubling_constant μ)^3) * μ (closed_ball x ε) :=
begin
  let C := doubling_constant μ,
  let h := exists_measure_closed_ball_le_mul' μ,
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
  cases le_or_gt 0 ε with hε hε,
  { exact closed_ball_subset_closed_ball (mul_le_mul_of_nonneg_right ht.2 hε), },
  { rw [closed_ball_eq_empty.mpr (mul_neg_of_pos_of_neg ht.1 hε),
        closed_ball_eq_empty.mpr (by linarith : 8 * ε < 0)], },
end

variables [proper_space α] [borel_space α] [is_locally_finite_measure μ]

/-- The Vitali family of a doubling measure. -/
def vitali_family : vitali_family μ :=
vitali.vitali_family μ ((doubling_constant μ)^3) $ λ x ε hε,
begin
  have h := forall_eventually_of_eventually_forall
    (exists_measure_closed_ball_le_mul_of_mem_Ioc μ 6 $ by norm_num),
  simpa only [exists_prop] using ((eventually_nhds_within_pos_mem_Ioc hε).and (h x)).exists,
end

/-- A version of *Lebesgue's density theorem* for a sequence of closed balls whose centres are
not required to be fixed.

See also `besicovitch.ae_tendsto_measure_inter_div`. -/
lemma ae_tendsto_measure_inter_div (S : set α) (K : ℝ) (hK : K ∈ unit_interval) :
  ∀ᵐ x ∂μ.restrict S, ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ)
    (δlim : tendsto δ l (𝓝[>] 0))
    (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (K * δ j)),
    tendsto (λ j, μ (S ∩ closed_ball (w j) (δ j)) / μ (closed_ball (w j) (δ j))) l (𝓝 1) :=
begin
  let v := is_doubling_measure.vitali_family μ,
  filter_upwards [v.ae_tendsto_measure_inter_div S] with x hx ι l w δ δlim xmem,
  have : tendsto (λ j, closed_ball (w j) (δ j)) l (v.filter_at x),
  { refine v.tendsto_filter_at_iff.mpr ⟨_, (λ ε hε, _)⟩,
    { simp only [v, vitali.vitali_family],
      have δpos : ∀ᶠ j in l, 0 < δ j := eventually_mem_of_tendsto_nhds_within δlim,
      replace xmem : ∀ᶠ (j : ι) in l, x ∈ closed_ball (w j) (δ j) := (δpos.and xmem).mono
        (λ j hj, closed_ball_subset_closed_ball (by nlinarith [hj.1, hK.2]) hj.2),
      apply ((δlim.eventually
        (exists_measure_closed_ball_le_mul_of_mem_Ioc μ 7 $ by norm_num)).and (xmem.and δpos)).mono,
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
      replace hK : 0 < K + 1 := by linarith [hK.1],
      apply (((metric.tendsto_nhds.mp δlim _ (div_pos hε hK)).and δpos).and xmem).mono,
      rintros j ⟨⟨hjε, hj₀ : 0 < δ j⟩, hx⟩ y hy,
      replace hjε : (K + 1) * δ j < ε :=
        by simpa [abs_eq_self.mpr hj₀.le] using (lt_div_iff' hK).mp hjε,
      simp only [mem_closed_ball] at hx hy ⊢,
      linarith [dist_triangle_right y x (w j)], } },
  exact hx.comp this,
end

end is_doubling_measure
