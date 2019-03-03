import topology.uniform_space.cauchy topology.uniform_space.separation

open filter
variables {α : Type*} [uniform_space α]

/-In a separated space, a complete set is closed -/
lemma is_closed_of_is_complete [separated α] {s : set α} (h : is_complete s) : is_closed s :=
is_closed_iff_nhds.2 $ λ a ha, begin
  let f := nhds a ⊓ principal s,
  have : cauchy f := cauchy_downwards (cauchy_nhds) ha (lattice.inf_le_left),
  rcases h f this (lattice.inf_le_right) with ⟨y, ys, fy⟩,
  rwa (tendsto_nhds_unique ha lattice.inf_le_left fy : a = y)
end
