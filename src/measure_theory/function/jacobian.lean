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

open measure_theory measure_theory.measure metric filter
open_locale nnreal ennreal topological_space pointwise

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  [measurable_space E] [borel_space E] (μ : measure E) [is_add_haar_measure μ]

lemma zoug (A : E →L[ℝ] E) {m : ℝ≥0∞} (hm : ennreal.of_real (abs (A : E →ₗ[ℝ] E).det) < m) :
  ∀ᶠ δ in 𝓝[≥] (0 : ℝ≥0), ∀ (s : set E) (f : E → E) (hf : lipschitz_on_with δ (f - A) s),
  μ (f '' s) ≤ m * μ s :=
begin
  -- construct a small neighborhood of `g '' (closed_ball 0 1)` with measure comparable to
    -- the determinant of `g`.
    obtain ⟨ε, hε, εpos⟩ : ∃ (ε : ℝ),
      μ (closed_ball 0 ε + A '' (closed_ball 0 1)) < m * μ (closed_ball 0 1) ∧ 0 < ε,
    { have HC : is_compact (A '' closed_ball 0 1) :=
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
      have L2 : tendsto (λ ε, μ (closed_ball 0 ε + g '' (closed_ball 0 1)))
        (𝓝[Ioi 0] 0) (𝓝 (d * μ (closed_ball 0 1))),
      { convert L1,
        exact (add_haar_image_continuous_linear_map _ _ _).symm },
      have I : d * μ (closed_ball 0 1) < m * μ (closed_ball 0 1) :=
        (ennreal.mul_lt_mul_right ((add_haar_closed_ball_pos μ _ zero_lt_one).ne')
          measure_closed_ball_lt_top.ne).2 hm,
      have H : ∀ᶠ (b : ℝ) in 𝓝[Ioi 0] 0,
        μ (closed_ball 0 b + ⇑g '' closed_ball 0 1) < m * μ (closed_ball 0 1) :=
          (tendsto_order.1 L2).2 _ I,
      exact (H.and self_mem_nhds_within).exists },
end
