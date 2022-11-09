/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.inner_product_space.projection

/-!
# Extension lemmas for dense subspaces

We provide a few lemmas that might be helpful to prove equalities in Hilbert spaces.

## Main statements

* `dense.ext_of_sub_mem_orthogonal`: If `S` is dense and `x - y ∈ Sᗮ`, then `x = y`.
* `dense.ext_inner_left`
* `dense.ext_inner_right`

-/

noncomputable theory
open submodule

variables {𝕜 E : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

variables {x y : E} {S : submodule 𝕜 E}

namespace dense
variables  [complete_space E]

/-- If `S` is dense and `x - y ∈ Sᗮ`, then `x = y`. -/
lemma ext_of_sub_mem_orthogonal (hS : dense (S : set E)) (h : x - y ∈ Sᗮ) : x = y :=
begin
  rw [dense_iff_topological_closure_eq_top, topological_closure_eq_top_iff] at hS,
  rwa [hS, mem_bot, sub_eq_zero] at h,
end

lemma ext_inner_left (hS : dense (S : set E)) (h : ∀ (v : S), ⟪x, v⟫ = ⟪y, v⟫) :
  x = y :=
hS.ext_of_sub_mem_orthogonal (submodule.sub_mem_orthogonal_of_inner_left h)

lemma ext_inner_right (hS : dense (S : set E))
  (h : ∀ (v : S), ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x = y :=
hS.ext_of_sub_mem_orthogonal (submodule.sub_mem_orthogonal_of_inner_right h)

end dense
