import algebra.algebra.subalgebra
import topology.algebra.continuous_functions
import topology.instances.real
import topology.algebra.ring

variables {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]

def separates_points (A : set C(X, Y)) : Prop :=
∀ x y : X, ∃ f ∈ A, (f : X → Y) x ≠ (f : X → Y) y

variables [t2_space X] [compact_space X]

theorem stone_weierstrass (A : subalgebra ℝ C(X, ℝ)) :
  separates_points A.carrier ↔ A.topological_closure = ⊤ :=
sorry
