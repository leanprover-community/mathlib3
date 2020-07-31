/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import topology.algebra.continuous_functions
import linear_algebra.affine_space

/-!
# Topological properties of affine spaces and maps

For now, this contains only a few facts regarding the continuity of affine maps in the special
case when the point space and vector space are the same.
-/

variables {R E F : Type*}
  [ring R]
  [add_comm_group E] [semimodule R E] [topological_space E]
  [add_comm_group F] [semimodule R F] [topological_space F] [topological_add_group F]

namespace affine_map

/-
TODO: Deal with the case where the point spaces are different from the vector spaces.
-/

/-- An affine map is continuous iff its underlying linear map is continuous. -/
lemma continuous_iff {f : affine_map R E E F F} :
  continuous f ↔ continuous f.linear :=
begin
  split,
  { intro hc,
    let f' : C(E, F) := ⟨f, hc⟩,
    let fconst : C(E, F) := ⟨(λ z, f 0), continuous_const⟩,
    let fdiff := f' - fconst,
    convert fdiff.2,
    rw [decomp' f],
    refl },
  { intro hc,
    let flin' : C(E, F) := ⟨f.linear, hc⟩,
    let fconst : C(E, F) := ⟨(λ z, f 0), continuous_const⟩,
    let f' := flin' + fconst,
    convert f'.2,
    rw [decomp f],
    refl }
end

/-- The line map is continuous. -/
lemma line_map_continuous [topological_space R] [topological_semimodule R F] {p v : F} :
  continuous (@line_map R F F _ _ _ _ p v) :=
begin
  refine continuous_iff.mpr _,
  change continuous ((λ z : R × F, z.1 • z.2) ∘ (λ z : R, (⟨z, v⟩ : R × F))),
  exact continuous.comp continuous_smul (by continuity),
end

end affine_map
