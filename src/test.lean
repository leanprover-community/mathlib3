import topology.algebra.const_mul_action
import group_theory.coset

noncomputable theory

variables {G : Type*} [group G] [topological_space G] {Γ : subgroup G} [t2_space G]
  [properly_discontinuous_smul Γ.opposite G] [has_continuous_const_smul Γ.opposite G]
  [locally_compact_space G]

/-- FAILS -/
example : t2_space (G ⧸ Γ) := by apply_instance

/-- Replace the reference to `quotient_group.left_rel` inside `has_quotient α (subgroup α)`
  instance with its definition. This is an argument for removing `quotient_group.left_rel`
  entirely. -/
@[priority 10000] instance (α : Type*) [group α] : has_quotient α (subgroup α) :=
  ⟨λ s, quotient (mul_action.orbit_rel s.opposite α)⟩

/-- SUCCEEDS -/
example : t2_space (G ⧸ Γ) := by apply_instance
