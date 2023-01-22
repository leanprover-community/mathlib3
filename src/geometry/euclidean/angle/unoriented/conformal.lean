/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.calculus.conformal.normed_space
import geometry.euclidean.angle.unoriented.basic

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/

namespace inner_product_geometry

variables {V : Type*} [inner_product_space ℝ V]

lemma is_conformal_map.preserves_angle {E F : Type*}
  [inner_product_space ℝ E] [inner_product_space ℝ F]
  {f' : E →L[ℝ] F} (h : is_conformal_map f') (u v : E) :
  angle (f' u) (f' v) = angle u v :=
begin
  obtain ⟨c, hc, li, rfl⟩ := h,
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)
end

/-- If a real differentiable map `f` is conformal at a point `x`,
    then it preserves the angles at that point. -/
lemma conformal_at.preserves_angle {E F : Type*}
  [inner_product_space ℝ E] [inner_product_space ℝ F]
  {f : E → F} {x : E} {f' : E →L[ℝ] F}
  (h : has_fderiv_at f f' x) (H : conformal_at f x) (u v : E) :
  angle (f' u) (f' v) = angle u v :=
let ⟨f₁, h₁, c⟩ := H in h₁.unique h ▸ is_conformal_map.preserves_angle c u v

end inner_product_geometry
