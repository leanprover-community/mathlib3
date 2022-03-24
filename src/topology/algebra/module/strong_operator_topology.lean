/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.algebra.module.basic
import topology.algebra.uniform_group
import topology.uniform_space.uniform_convergence_space

/-!
# TODO
-/

variables (𝕜 E F : Type*) [add_comm_group E] [add_comm_group F] [semiring 𝕜]
  [module 𝕜 E] [module 𝕜 F] [topological_space E] [topological_space F] [topological_space 𝕜]
  [topological_add_group E] [topological_add_group F] [has_continuous_smul 𝕜 E]
  [has_continuous_smul 𝕜 F] (𝔖 : set (set E))

namespace strong_topology

protected def topological_space : topological_space (E →L[𝕜] F) :=
topological_space.induced (coe_fn : (E →L[𝕜] F) → (E → F))
  (@uniform_convergence_on.uniform_space _ _
    (topological_add_group.to_uniform_space _) 𝔖).to_topological_space

end strong_topology
