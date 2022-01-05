/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import topology.algebra.filter_basis
import topology.algebra.uniform_group

/-!
# Uniform properties of neighborhood bases in topological algebra

This files contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/

open_locale uniformity filter
open filter

namespace add_group_filter_basis

variables {G : Type*} [add_comm_group G] (B : add_group_filter_basis G)

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
protected def uniform_space : uniform_space G :=
@topological_add_group.to_uniform_space G _ B.topology B.is_topological_add_group

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected lemma uniform_add_group : @uniform_add_group G B.uniform_space _:=
@topological_add_group_is_uniform G _ B.topology B.is_topological_add_group

lemma cauchy_iff {F : filter G} :
  @cauchy G B.uniform_space F ↔ F.ne_bot ∧ ∀ U ∈ B, ∃ M ∈ F, ∀ x y ∈ M, y - x ∈ U :=
begin
  letI := B.uniform_space,
  haveI := B.uniform_add_group,
  suffices : F ×ᶠ F ≤ 𝓤 G ↔ ∀ U ∈ B, ∃ M ∈ F, ∀ x y ∈ M, y - x ∈ U,
    by split ; rintros ⟨h', h⟩ ; refine ⟨h', _⟩ ; [rwa ← this, rwa this],
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap],
  change tendsto _ _ _ ↔ _,
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_has_basis, BINDER_UPDATE_LEMMA]
end

end add_group_filter_basis
