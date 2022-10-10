/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.covering.vitali
import measure_theory.covering.differentiation
import analysis.special_functions.log.base

/-!
# Doubling measures and Lebesgue's density theorem

A doubling measure `μ` on a metric space is a measure for which there exists a constant `C` such
that for all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

Lebesgue's density theorem states that given a set `S` in a sigma compact metric space with
locally-finite doubling measure `μ` then for almost all points `x` in `S`, for any sequence of
closed balls `B₀, B₁, B₂, ...` containing `x`, the limit `μ (S ∩ Bⱼ) / μ (Bⱼ) → 1` as `j → ∞`.

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

open set filter metric measure_theory topological_space
open_locale nnreal topological_space

local attribute [instance] emetric.second_countable_of_sigma_compact

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

section
variables [second_countable_topology α] [borel_space α] [is_locally_finite_measure μ]

open_locale topological_space

/-- A Vitali family in a space with a doubling measure, designed so that the sets at `x` contain
all `closed_ball y r` when `dist x y ≤ K * r`. -/
@[irreducible] def vitali_family (K : ℝ) : vitali_family μ :=
begin
  /- the Vitali covering theorem gives a family that works well at small scales, thanks to the
  doubling property. We enlarge this family to add large sets, to make sure that all balls and not
  only small ones belong to the family, for convenience. -/
  let R := scaling_scale_of μ (max (4 * K + 3) 3),
  have Rpos : 0 < R := scaling_scale_of_pos _ _,
  have A : ∀ (x : α), ∃ᶠ r in 𝓝[>] (0 : ℝ),
    μ (closed_ball x (3 * r)) ≤ scaling_constant_of μ (max (4 * K + 3) 3) * μ (closed_ball x r),
  { assume x,
    apply frequently_iff.2 (λ U hU, _),
    obtain ⟨ε, εpos, hε⟩ := mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 hU,
    refine ⟨min ε R, hε ⟨lt_min εpos Rpos, min_le_left _ _⟩, _⟩,
    exact measure_mul_le_scaling_constant_of_mul μ
      ⟨zero_lt_three, le_max_right _ _⟩ (min_le_right _ _) },
  exact (vitali.vitali_family μ (scaling_constant_of μ (max (4 * K + 3) 3)) A).enlarge
    (R / 4) (by linarith),
end

/-- In the Vitali family `is_doubling_measure.vitali_family K`, the sets based at `x` contain all
balls `closed_ball y r` when `dist x y ≤ K * r`. -/
lemma closed_ball_mem_vitali_family_of_dist_le_mul
  {K : ℝ} {x y : α} {r : ℝ} (h : dist x y ≤ K * r) (rpos : 0 < r) :
  closed_ball y r ∈ (vitali_family μ K).sets_at x :=
begin
  let R := scaling_scale_of μ (max (4 * K + 3) 3),
  simp only [vitali_family, vitali_family.enlarge, vitali.vitali_family, mem_union, mem_set_of_eq,
    is_closed_ball, true_and, (nonempty_ball.2 rpos).mono ball_subset_interior_closed_ball,
    measurable_set_closed_ball],
  /- The measure is doubling on scales smaller than `R`. Therefore, we treat differently small
  and large balls. For large balls, this follows directly from the enlargement we used in the
  definition. -/
  by_cases H : closed_ball y r ⊆ closed_ball x (R / 4),
  swap, { exact or.inr H },
  left,
  /- For small balls, there is the difficulty that `r` could be large but still the ball could be
  small, if the annulus `{y | ε ≤ dist y x ≤ R/4}` is empty. We split between the cases `r ≤ R`
  and `r < R`, and use the doubling for the former and rough estimates for the latter. -/
  rcases le_or_lt r R with hr|hr,
  { refine ⟨(K + 1) * r, _⟩,
    split,
    { apply closed_ball_subset_closed_ball',
      rw dist_comm,
      linarith },
    { have I1 : closed_ball x (3 * ((K + 1) * r)) ⊆ closed_ball y ((4 * K + 3) * r),
      { apply closed_ball_subset_closed_ball',
        linarith },
      have I2 : closed_ball y ((4 * K + 3) * r) ⊆ closed_ball y ((max (4 * K + 3) 3) * r),
      { apply closed_ball_subset_closed_ball,
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) rpos.le },
      apply (measure_mono (I1.trans I2)).trans,
      exact measure_mul_le_scaling_constant_of_mul _
        ⟨zero_lt_three.trans_le (le_max_right _ _), le_rfl⟩ hr } },
  { refine ⟨R / 4, H, _⟩,
    have : closed_ball x (3 * (R / 4)) ⊆ closed_ball y r,
    { apply closed_ball_subset_closed_ball',
      have A : y ∈ closed_ball y r, from mem_closed_ball_self rpos.le,
      have B := mem_closed_ball'.1 (H A),
      linarith },
    apply (measure_mono this).trans _,
    refine le_mul_of_one_le_left (zero_le _) _,
    exact ennreal.one_le_coe_iff.2 (le_max_right _ _) }
end

lemma tendsto_closed_ball_filter_at {K : ℝ} {x : α} {ι : Type*} {l : filter ι}
  (w : ι → α) (δ : ι → ℝ) (δlim : tendsto δ l (𝓝[>] 0))
  (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (K * δ j)) :
  tendsto (λ j, closed_ball (w j) (δ j)) l ((vitali_family μ K).filter_at x) :=
begin
  refine (vitali_family μ K).tendsto_filter_at_iff.mpr ⟨_, λ ε hε, _⟩,
  { filter_upwards [xmem, δlim self_mem_nhds_within] with j hj h'j,
    exact closed_ball_mem_vitali_family_of_dist_le_mul μ hj h'j },
  { by_cases l.ne_bot,
    swap, { simp [not_ne_bot.1 h] },
    have hK : 0 ≤ K,
    { resetI,
      rcases (xmem.and (δlim self_mem_nhds_within)).exists with ⟨j, hj, h'j⟩,
      have : 0 ≤ K * δ j := nonempty_closed_ball.1 ⟨x, hj⟩,
      exact (mul_nonneg_iff_left_nonneg_of_pos (mem_Ioi.1 h'j)).1 this },
    have δpos := eventually_mem_of_tendsto_nhds_within δlim,
    replace δlim := tendsto_nhds_of_tendsto_nhds_within δlim,
    replace hK : 0 < K + 1, by linarith,
    apply (((metric.tendsto_nhds.mp δlim _ (div_pos hε hK)).and δpos).and xmem).mono,
    rintros j ⟨⟨hjε, hj₀ : 0 < δ j⟩, hx⟩ y hy,
    replace hjε : (K + 1) * δ j < ε :=
      by simpa [abs_eq_self.mpr hj₀.le] using (lt_div_iff' hK).mp hjε,
    simp only [mem_closed_ball] at hx hy ⊢,
    linarith [dist_triangle_right y x (w j)] }
end

end

/-- A version of *Lebesgue's density theorem* for a sequence of closed balls whose centres are
not required to be fixed.

See also `besicovitch.ae_tendsto_measure_inter_div`. -/
lemma ae_tendsto_measure_inter_div
  [sigma_compact_space α] [borel_space α] [is_locally_finite_measure μ] (S : set α) (K : ℝ) :
  ∀ᵐ x ∂μ.restrict S, ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ)
    (δlim : tendsto δ l (𝓝[>] 0))
    (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (K * δ j)),
    tendsto (λ j, μ (S ∩ closed_ball (w j) (δ j)) / μ (closed_ball (w j) (δ j))) l (𝓝 1) :=
by filter_upwards [(vitali_family μ K).ae_tendsto_measure_inter_div S] with x hx ι l w δ δlim xmem
using hx.comp (tendsto_closed_ball_filter_at μ _ _ δlim xmem)

end is_doubling_measure
