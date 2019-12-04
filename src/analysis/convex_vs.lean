import analysis.convex
import topology.algebra.module

section topological_vector_space

variables {α : Type*} [add_comm_group α] [vector_space ℝ α]
[topological_space α] [topological_add_group α] [topological_vector_space ℝ α]

local attribute [instance] set.pointwise_add

/-- In a topological vector space, the interior of a convex set is convex. -/
lemma convex_interior {A : set α} (hA : convex A) : convex (interior A) :=
λ x y a b hx hy ha hb hab,
let aA := (λ x, a • x) '' (interior A) in
let bA := (λ x, b • x) '' (interior A) in
or.elim (eq_or_lt_of_le ha)
(λ heq,
  have hb₁: b = 1, by rwa [←heq, zero_add] at hab,
  by rwa [←heq, zero_smul, zero_add, hb₁, one_smul])
(λ hlt, 
  have haA : is_open aA, from
    (is_open_map_smul_of_ne_zero (ne_of_gt hlt) _) is_open_interior,
  mem_interior.2 $ exists.intro (aA + bA)
  ⟨λ w ⟨ax', ⟨x', hx', hax'⟩, by', ⟨y', hy', hby'⟩, hw⟩,
  by { rw [←hax', ←hby'] at hw, rw hw, exact hA
    _ _ _ _ (interior_subset hx') (interior_subset hy') ha hb hab },
  is_open_pointwise_add_right haA,
  ⟨_, ⟨_, hx, rfl⟩, _, ⟨_, hy, rfl⟩, rfl⟩⟩)

/-- In a topological vector space, the closure of a convex set is convex. -/
lemma convex_closure {A : set α} (hA : convex A) : convex (closure A) :=
sorry

end topological_vector_space
