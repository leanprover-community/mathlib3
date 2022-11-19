/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.special_functions.log.base
import measure_theory.measure.measure_space_def

/-!
# Doubling measures

A doubling measure `μ` on a metric space is a measure for which there exists a constant `C` such
that for all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

This file records basic files on doubling measures.

## Main definitions

  * `is_doubling_measure`: the definition of a doubling measure (as a typeclass).
  * `is_doubling_measure.doubling_constant`: a function yielding the doubling constant `C` appearing
  in the definition of a doubling measure.
-/

noncomputable theory

open set filter metric measure_theory topological_space
open_locale nnreal topological_space

/-- A measure `μ` is said to be a doubling measure if there exists a constant `C` such that for
all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius `2 * ε` is
bounded by `C` times the measure of the concentric ball of radius `ε`.

Note: it is important that this definition makes a demand only for sufficiently small `ε`. For
example we want hyperbolic space to carry the instance `is_doubling_measure volume` but volumes grow
exponentially in hyperbolic space. To be really explicit, consider the hyperbolic plane of
curvature -1, the area of a disc of radius `ε` is `A(ε) = 2π(cosh(ε) - 1)` so `A(2ε)/A(ε) ~ exp(ε)`.
-/
class is_doubling_measure {α : Type*} [metric_space α] [measurable_space α] (μ : measure α) :=
(exists_measure_closed_ball_le_mul [] :
  ∃ (C : ℝ≥0), ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (2 * ε)) ≤ C * μ (closed_ball x ε))

namespace is_doubling_measure

variables {α : Type*} [metric_space α] [measurable_space α] (μ : measure α) [is_doubling_measure μ]

/-- A doubling constant for a doubling measure.

See also `is_doubling_measure.scaling_constant_of`. -/
def doubling_constant : ℝ≥0 := classical.some $ exists_measure_closed_ball_le_mul μ

lemma exists_measure_closed_ball_le_mul' :
  ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closed_ball x (2 * ε)) ≤ doubling_constant μ * μ (closed_ball x ε) :=
classical.some_spec $ exists_measure_closed_ball_le_mul μ

lemma exists_eventually_forall_measure_closed_ball_le_mul (K : ℝ) :
  ∃ (C : ℝ≥0), ∀ᶠ ε in 𝓝[>] 0, ∀ x t (ht : t ≤ K),
    μ (closed_ball x (t * ε)) ≤ C * μ (closed_ball x ε) :=
begin
  let C := doubling_constant μ,
  have hμ : ∀ (n : ℕ), ∀ᶠ ε in 𝓝[>] 0, ∀ x,
    μ (closed_ball x (2^n * ε)) ≤ ↑(C^n) * μ (closed_ball x ε),
  { intros n,
    induction n with n ih, { simp, },
    replace ih := eventually_nhds_within_pos_mul_left (two_pos : 0 < (2 : ℝ)) ih,
    refine (ih.and (exists_measure_closed_ball_le_mul' μ)).mono (λ ε hε x, _),
    calc μ (closed_ball x (2^(n + 1) * ε))
          = μ (closed_ball x (2^n * (2 * ε))) : by rw [pow_succ', mul_assoc]
      ... ≤ ↑(C^n) * μ (closed_ball x (2 * ε)) : hε.1 x
      ... ≤ ↑(C^n) * (C * μ (closed_ball x ε)) : ennreal.mul_left_mono (hε.2 x)
      ... = ↑(C^(n + 1)) * μ (closed_ball x ε) : by rw [← mul_assoc, pow_succ', ennreal.coe_mul], },
  rcases lt_or_le K 1 with hK | hK,
  { refine ⟨1, _⟩,
    simp only [ennreal.coe_one, one_mul],
    exact eventually_mem_nhds_within.mono (λ ε hε x t ht,
      measure_mono $ closed_ball_subset_closed_ball (by nlinarith [mem_Ioi.mp hε])), },
  { refine ⟨C^⌈real.logb 2 K⌉₊, ((hμ ⌈real.logb 2 K⌉₊).and eventually_mem_nhds_within).mono
      (λ ε hε x t ht, le_trans (measure_mono $ closed_ball_subset_closed_ball _) (hε.1 x))⟩,
    refine mul_le_mul_of_nonneg_right (ht.trans _) (mem_Ioi.mp hε.2).le,
    conv_lhs { rw ← real.rpow_logb two_pos (by norm_num) (by linarith : 0 < K), },
    rw ← real.rpow_nat_cast,
    exact real.rpow_le_rpow_of_exponent_le one_le_two (nat.le_ceil (real.logb 2 K)), },
end

/-- A variant of `is_doubling_measure.doubling_constant` which allows for scaling the radius by
values other than `2`. -/
def scaling_constant_of (K : ℝ) : ℝ≥0 :=
max (classical.some $ exists_eventually_forall_measure_closed_ball_le_mul μ K) 1

lemma eventually_measure_mul_le_scaling_constant_of_mul (K : ℝ) :
  ∃ (R : ℝ), 0 < R ∧ ∀ x t r (ht : t ∈ Ioc 0 K) (hr : r ≤ R),
    μ (closed_ball x (t * r)) ≤ scaling_constant_of μ K * μ (closed_ball x r) :=
begin
  have h := classical.some_spec (exists_eventually_forall_measure_closed_ball_le_mul μ K),
  rcases mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩,
  refine ⟨R, Rpos, λ x t r ht hr, _⟩,
  rcases lt_trichotomy r 0 with rneg|rfl|rpos,
  { have : t * r < 0, from mul_neg_of_pos_of_neg ht.1 rneg,
    simp only [closed_ball_eq_empty.2 this, measure_empty, zero_le'] },
  { simp only [mul_zero, closed_ball_zero],
    refine le_mul_of_one_le_of_le _ le_rfl,
    apply ennreal.one_le_coe_iff.2 (le_max_right _ _) },
  { apply (hR ⟨rpos, hr⟩ x t ht.2).trans _,
    exact ennreal.mul_le_mul (ennreal.coe_le_coe.2 (le_max_left _ _)) le_rfl }
end

/-- A scale below which the doubling measure `μ` satisfies good rescaling properties when one
multiplies the radius of balls by at most `K`, as stated
in `measure_mul_le_scaling_constant_of_mul`. -/
def scaling_scale_of (K : ℝ) : ℝ :=
(eventually_measure_mul_le_scaling_constant_of_mul μ K).some

lemma scaling_scale_of_pos (K : ℝ) : 0 < scaling_scale_of μ K :=
(eventually_measure_mul_le_scaling_constant_of_mul μ K).some_spec.1

lemma measure_mul_le_scaling_constant_of_mul {K : ℝ} {x : α} {t r : ℝ}
  (ht : t ∈ Ioc 0 K) (hr : r ≤ scaling_scale_of μ K) :
  μ (closed_ball x (t * r)) ≤ scaling_constant_of μ K * μ (closed_ball x r) :=
(eventually_measure_mul_le_scaling_constant_of_mul μ K).some_spec.2 x t r ht hr

end is_doubling_measure
