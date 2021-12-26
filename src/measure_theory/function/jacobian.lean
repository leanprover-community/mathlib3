/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.covering.besicovitch_vector_space
import measure_theory.measure.haar_lebesgue
import analysis.normed_space.pointwise

/-!
# Change of variables in higher-dimensional integrals
-/

open measure_theory measure_theory.measure metric filter set
open_locale nnreal ennreal topological_space pointwise

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  [measurable_space E] [borel_space E] (μ : measure E) [is_add_haar_measure μ]

lemma zoug (A : E →L[ℝ] E) {m : ℝ≥0∞} (hm : ennreal.of_real (abs (A : E →ₗ[ℝ] E).det) < m) :
  ∀ᶠ δ in 𝓝 (0 : ℝ≥0), ∀ (s : set E) (f : E → E) (hf : lipschitz_on_with δ (f - A) s),
  μ (f '' s) ≤ m * μ s :=
begin
  let d := ennreal.of_real (abs (A : E →ₗ[ℝ] E).det),
  -- construct a small neighborhood of `A '' (closed_ball 0 1)` with measure comparable to
  -- the determinant of `A`.
  obtain ⟨ε, hε, εpos⟩ : ∃ (ε : ℝ),
    μ (closed_ball 0 ε + A '' (closed_ball 0 1)) < m * μ (closed_ball 0 1) ∧ 0 < ε,
  sorry; { have HC : is_compact (A '' closed_ball 0 1) :=
      (proper_space.is_compact_closed_ball _ _).image A.continuous,
    have L0 : tendsto (λ ε, μ (cthickening ε (A '' (closed_ball 0 1))))
      (𝓝[>] 0) (𝓝 (μ (A '' (closed_ball 0 1)))),
    { apply tendsto.mono_left _ nhds_within_le_nhds,
      exact tendsto_measure_cthickening_of_is_compact HC },
    have L1 : tendsto (λ ε, μ (closed_ball 0 ε + A '' (closed_ball 0 1)))
      (𝓝[>] 0) (𝓝 (μ (A '' (closed_ball 0 1)))),
    { apply L0.congr' _,
      filter_upwards [self_mem_nhds_within],
      assume r hr,
      rw [HC.cthickening_eq_add_closed_ball (le_of_lt hr), add_comm] },
    have L2 : tendsto (λ ε, μ (closed_ball 0 ε + A '' (closed_ball 0 1)))
      (𝓝[>] 0) (𝓝 (d * μ (closed_ball 0 1))),
    { convert L1,
      exact (add_haar_image_continuous_linear_map _ _ _).symm },
    have I : d * μ (closed_ball 0 1) < m * μ (closed_ball 0 1) :=
      (ennreal.mul_lt_mul_right ((add_haar_closed_ball_pos μ _ zero_lt_one).ne')
        measure_closed_ball_lt_top.ne).2 hm,
    have H : ∀ᶠ (b : ℝ) in 𝓝[>] 0,
      μ (closed_ball 0 b + A '' closed_ball 0 1) < m * μ (closed_ball 0 1) :=
        (tendsto_order.1 L2).2 _ I,
    exact (H.and self_mem_nhds_within).exists },
  have : Iio (⟨ε, εpos.le⟩ : ℝ≥0) ∈ 𝓝 (0 : ℝ≥0),
  { apply Iio_mem_nhds, exact εpos },
  filter_upwards [this],
  assume δ hδ s f hf,
  have : ∀ x r, x ∈ s → μ (f '' (s ∩ closed_ball x r)) ≤ m * μ (closed_ball x r),
  { assume x r xs,
    have : f '' (s ∩ closed_ball x r) ⊆ A '' (closed_ball 0 r) + closed_ball (f x) (ε * r),
    sorry; { rintros y ⟨z, ⟨zs, zr⟩, rfl⟩,
      apply set.mem_add.2 ⟨A (z - x), (f - A) z - (f - A) x + f x, _, _, _⟩,
      { apply mem_image_of_mem,
        simpa [dist_eq_norm] using zr },
      { rw [mem_closed_ball_iff_norm, add_sub_cancel, ← dist_eq_norm],
        calc dist ((f - A) z) ((f - A) x)
            ≤ δ * dist z x : hf.dist_le_mul _ zs _ xs
        ... ≤ ε * r : mul_le_mul (le_of_lt hδ) zr dist_nonneg εpos.le },
      { simp only [map_sub, pi.sub_apply],
        abel } },

  }
end

#exit

f z = (f - A) z - (f - A) x + A (z - x) + f x
