/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.lie_group
import analysis.normed_space.units

/-!
# Units of normed algebra
-/

noncomputable theory

instance is_units_of_normed_algebra.charted_space {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  charted_space R {x : R | is_unit x} :=
topological_space.opens.charted_space ⟨({x : R | is_unit x} : set R), units.is_open⟩

instance is_units_of_normed_algebra.smooth_manifold_with_corners
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  smooth_manifold_with_corners (model_with_corners_self 𝕜 R) {x : R | is_unit x} :=
topological_space.opens.smooth_manifold_with_corners (model_with_corners_self 𝕜 R)
  ⟨({x : R | is_unit x} : set R), units.is_open⟩

instance units_of_normed_algebra.charted_space {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  charted_space R (units R) :=
is_unit.subtype_homeomorph.charted_space R

instance units_of_normed_algebra.smooth_manifold_with_corners
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] :
  smooth_manifold_with_corners (model_with_corners_self 𝕜 R) (units R) :=
is_unit.subtype_homeomorph.smooth_manifold_with_corners (model_with_corners_self 𝕜 R)
