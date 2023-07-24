/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import geometry.manifold.smooth_manifold_with_corners
import topology.paracompact
import topology.metric_space.metrizable

/-!
# Metrizability of a σ-compact manifold

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we show that a σ-compact Hausdorff topological manifold over a finite dimensional real
vector space is metrizable.
-/

open topological_space

/-- A σ-compact Hausdorff topological manifold over a finite dimensional real vector space is
metrizable. -/
lemma manifold_with_corners.metrizable_space
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
  (M : Type*) [topological_space M] [charted_space H M]
  [sigma_compact_space M] [t2_space M] : metrizable_space M :=
begin
  haveI := I.locally_compact, haveI := charted_space.locally_compact H M,
  haveI : normal_space M := normal_of_paracompact_t2,
  haveI := I.second_countable_topology,
  haveI := charted_space.second_countable_of_sigma_compact H M,
  exact metrizable_space_of_t3_second_countable M
end
