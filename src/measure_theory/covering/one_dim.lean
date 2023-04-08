/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.covering.density_theorem
import measure_theory.measure.haar_lebesgue

/-!
# Covering theorems for Lebesgue measure in one dimension

We have a general theory of covering theorems for doubling measures, developed notably
in `density_theorems.lean`. In this file, we expand the API for this theory in one dimension,
by showing that intervals belong to the relevant Vitali family.
-/

open set measure_theory is_doubling_measure filter
open_locale topology

namespace real

lemma Icc_mem_vitali_family_at_right {x y : ℝ} (hxy : x < y) :
  Icc x y ∈ (vitali_family (volume : measure ℝ) 1).sets_at x :=
begin
  rw Icc_eq_closed_ball,
  refine closed_ball_mem_vitali_family_of_dist_le_mul _ _ (by linarith),
  rw [dist_comm, real.dist_eq, abs_of_nonneg];
  linarith,
end

lemma tendsto_Icc_vitali_family_right (x : ℝ) :
  tendsto (λ y, Icc x y) (𝓝[>] x) ((vitali_family (volume : measure ℝ) 1).filter_at x) :=
begin
  refine (vitali_family.tendsto_filter_at_iff _).2 ⟨_, _⟩,
  { filter_upwards [self_mem_nhds_within] with y hy using Icc_mem_vitali_family_at_right hy },
  { assume ε εpos,
    have : x ∈ Ico x (x + ε) := ⟨le_refl _, by linarith⟩,
    filter_upwards [Icc_mem_nhds_within_Ioi this] with y hy,
    rw closed_ball_eq_Icc,
    exact Icc_subset_Icc (by linarith) hy.2 }
end

lemma Icc_mem_vitali_family_at_left {x y : ℝ} (hxy : x < y) :
  Icc x y ∈ (vitali_family (volume : measure ℝ) 1).sets_at y :=
begin
  rw Icc_eq_closed_ball,
  refine closed_ball_mem_vitali_family_of_dist_le_mul _ _ (by linarith),
  rw [real.dist_eq, abs_of_nonneg];
  linarith,
end

lemma tendsto_Icc_vitali_family_left (x : ℝ) :
  tendsto (λ y, Icc y x) (𝓝[<] x) ((vitali_family (volume : measure ℝ) 1).filter_at x) :=
begin
  refine (vitali_family.tendsto_filter_at_iff _).2 ⟨_, _⟩,
  { filter_upwards [self_mem_nhds_within] with y hy using Icc_mem_vitali_family_at_left hy },
  { assume ε εpos,
    have : x ∈ Ioc (x - ε) x := ⟨by linarith, le_refl _⟩,
    filter_upwards [Icc_mem_nhds_within_Iio this] with y hy,
    rw closed_ball_eq_Icc,
    exact Icc_subset_Icc hy.1 (by linarith) }
end

end real
