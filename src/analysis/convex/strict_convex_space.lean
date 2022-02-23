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

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strict_convex_closed_ball` below.

See also `strict_convex_space.of_strict_convex_closed_unit_ball`. -/
class strict_convex_space (𝕜 E : Type*) [normed_linear_ordered_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] : Prop :=
(strict_convex_closed_ball : ∀ r : ℝ, 0 < r → strict_convex 𝕜 (closed_ball (0 : E) r))

variables (𝕜 : Type*) {E : Type*} [normed_linear_ordered_field 𝕜]

variables [normed_group E] [normed_space 𝕜 E]

/-- A closed ball in a strictly convex space is strictly convex. -/
lemma strict_convex_closed_ball [strict_convex_space 𝕜 E] (x : E) (r : ℝ) :
  strict_convex 𝕜 (closed_ball x r) :=
begin
  cases le_or_lt r 0 with hr hr,
  { exact (subsingleton_closed_ball x hr).strict_convex },
  rw ← vadd_closed_ball_zero,
  exact (strict_convex_space.strict_convex_closed_ball r hr).vadd _,
end

/-- A real normed vector space is strictly convex provided that the unit ball is strictly convex. -/
lemma strict_convex_space.of_strict_convex_closed_unit_ball [normed_space ℝ E]
  [linear_map.compatible_smul E E 𝕜 ℝ] (h : strict_convex 𝕜 (closed_ball (0 : E) 1)) :
  strict_convex_space 𝕜 E :=
⟨λ r hr, by simpa only [smul_closed_unit_ball_of_nonneg hr.le] using h.smul r⟩
