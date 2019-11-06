/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/
import topology.uniform_space.cauchy topology.uniform_space.separation
import topology.dense_embedding

open filter
variables {α : Type*}

/-In a separated space, a complete set is closed -/
lemma is_closed_of_is_complete  [uniform_space α] [separated α] {s : set α} (h : is_complete s) :
  is_closed s :=
is_closed_iff_nhds.2 $ λ a ha, begin
  let f := nhds a ⊓ principal s,
  have : cauchy f := cauchy_downwards (cauchy_nhds) ha (lattice.inf_le_left),
  rcases h f this (lattice.inf_le_right) with ⟨y, ys, fy⟩,
  rwa (tendsto_nhds_unique ha lattice.inf_le_left fy : a = y)
end

namespace dense_inducing
open filter
variables [topological_space α] {β : Type*} [topological_space β]
variables {γ : Type*} [uniform_space γ] [complete_space γ] [separated γ]

lemma continuous_extend_of_cauchy {e : α → β} {f : α → γ}
  (de : dense_inducing e) (h : ∀ b : β, cauchy (map f (comap e $ nhds b))) :
  continuous (de.extend f) :=
de.continuous_extend $ λ b, complete_space.complete (h b)

end dense_inducing
