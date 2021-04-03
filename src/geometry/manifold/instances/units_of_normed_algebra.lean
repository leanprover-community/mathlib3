/-
Copyright © 2021 Heather Macbeth, Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Nicolò Cavalleri
-/

import geometry.manifold.algebra.lie_group
import analysis.normed_space.units

/-!
# Units of normed algebra
-/

noncomputable theory

instance units_of_normed_algebra.charted_space {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  charted_space R (units R) :=
units.open_embedding_coe.charted_space

namespace units

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R]

/- Why does it not find the 𝕜 alone? -/
@[simp, mfld_simps] lemma chart_at.apply {a : units R} {b : units R} :
  @chart_at R _ _ _ (@units_of_normed_algebra.charted_space 𝕜 _ _ _ _ _) a b = b := rfl

@[simp, mfld_simps] lemma chart_at.source {a : units R} :
  (@chart_at R _ _ _ (@units_of_normed_algebra.charted_space 𝕜 _ _ _ _ _) a).source = set.univ :=
rfl

end units

instance units_of_normed_algebra.smooth_manifold_with_corners
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  smooth_manifold_with_corners (model_with_corners_self 𝕜 R) (units R) :=
units.open_embedding_coe.singleton_smooth_manifold_with_corners (model_with_corners_self 𝕜 R)
