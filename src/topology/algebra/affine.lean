/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import topology.continuous_function.algebra
import linear_algebra.affine_space.affine_map

/-!
# Topological properties of affine spaces and maps

For now, this contains only a few facts regarding the continuity of affine maps in the special
case when the point space and vector space are the same.

TODO: Deal with the case where the point spaces are different from the vector spaces.
-/

namespace affine_map

variables {R E F : Type*}
variables [add_comm_group E] [topological_space E]
variables [add_comm_group F] [topological_space F] [topological_add_group F]

section ring

variables [ring R] [module R E] [module R F]

/-- An affine map is continuous iff its underlying linear map is continuous. -/
lemma continuous_iff {f : E →ᵃ[R] F} :
  continuous f ↔ continuous f.linear :=
begin
  split,
  { intro hc,
    rw decomp' f,
    have := hc.sub continuous_const,
    exact this, },
  { intro hc,
    rw decomp f,
    have := hc.add continuous_const,
    exact this }
end

/-- The line map is continuous. -/
@[continuity]
lemma line_map_continuous [topological_space R] [has_continuous_smul R F] {p v : F} :
  continuous ⇑(line_map p v : R →ᵃ[R] F) :=
continuous_iff.mpr $ (continuous_id.smul continuous_const).add $
  @continuous_const _ _ _ _ (0 : F)

end ring

section comm_ring

variables [comm_ring R] [module R F] [topological_space R] [has_continuous_smul R F]

@[continuity]
lemma homothety_continuous (x : F) (t : R) : continuous $ homothety x t :=
begin
  suffices : ⇑(homothety x t) = λ y, t • (y - x) + x, { rw this, continuity, },
  ext y,
  simp [homothety_apply],
end

end comm_ring

section field

variables [field R] [module R F] [topological_space R] [has_continuous_smul R F]

lemma homothety_is_open_map (x : F) (t : R) (ht : t ≠ 0) : is_open_map $ homothety x t :=
begin
  apply is_open_map.of_inverse (homothety_continuous x t⁻¹);
  intros e;
  simp [← affine_map.comp_apply, ← homothety_mul, ht],
end

end field

end affine_map
