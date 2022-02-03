/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.strict
import analysis.normed_space.ordered
import analysis.normed_space.pointwise

/-!
# Strictly convex spaces

This file defines strictly convex spaces. A normed space is strictly convex if all closed balls are
strictly convex. This does **not** mean that the norm is strictly convex (in fact, it never is).
-/

open metric
open_locale pointwise

/-- A strictly convex space is a normed space where the closed balls are strictly convex. -/
class strict_convex_space (𝕜 E : Type*) [normed_linear_ordered_field 𝕜] [semi_normed_group E]
  [normed_space 𝕜 E] : Prop :=
(strict_convex_closed_ball (r : ℝ) : strict_convex 𝕜 (closed_ball (0 : E) r))

variables (𝕜 : Type*) {E : Type*} [normed_linear_ordered_field 𝕜]

section semi_normed_group
variables [semi_normed_group E] [normed_space 𝕜 E]

lemma strict_convex_closed_ball [strict_convex_space 𝕜 E] (x : E) (r : ℝ) :
  strict_convex 𝕜 (closed_ball x r) :=
begin
  rw closed_ball_isometry,
  exact strict_convex.vadd (strict_convex_space.strict_convex_closed_ball r) _,
end

/-- For a space to be strictly convex, we only need to check nonempty closed balls. -/
lemma strict_convex_space.of_strict_convex_ball_nonneg
  (h : ∀ r, 0 ≤ r → strict_convex 𝕜 (closed_ball (0 : E) r)) :
  strict_convex_space 𝕜 E :=
⟨λ r, begin
  refine (le_or_lt 0 r).elim (h _) (λ hr, _),
  rw closed_ball_eq_empty.2 hr,
  exact strict_convex_empty,
end⟩

end semi_normed_group

section normed_group
variables [normed_group E] [normed_space 𝕜 E]

/-- For a space to be strictly convex, we only need to check the closed unit balls. -/
lemma strict_convex_space.of_strict_convex_closed_unit_ball [has_scalar 𝕜 ℝ] [normed_space ℝ E]
  [is_scalar_tower 𝕜 ℝ E] (h : strict_convex 𝕜 (closed_ball (0 : E) 1)) :
  strict_convex_space 𝕜 E :=
strict_convex_space.of_strict_convex_ball_nonneg _ $ λ r hr,
  by { convert h.smul r, rw [smul_closed_unit_ball, real.norm_of_nonneg hr] }

end normed_group
