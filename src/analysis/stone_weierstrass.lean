import algebra.algebra.subalgebra
import topology.algebra.continuous_functions
import topology.instances.real
import topology.algebra.algebra
import topology.algebra.continuous_functions
import topology.algebra.polynomial
import topology.bounded_continuous_function

variables {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]

/-- A set of continuous functions "separates points"
if for each pair of points there is a function taking different values on them. -/
def separates_points (A : set C(X, Y)) : Prop :=
∀ x y : X, ∃ f ∈ A, (f : X → Y) x ≠ (f : X → Y) y

variables [t2_space X] [compact_space X]

open_locale bounded_continuous_function

-- example : topological_space C(X, ℝ) := by apply_instance
noncomputable
example : topological_space (X →ᵇ ℝ) := by apply_instance

theorem stone_weierstrass (A : subalgebra ℝ C(X, ℝ)) :
  separates_points (A : set C(X, ℝ)) ↔ A.topological_closure = ⊤ :=
sorry

def polynomial_subalgebra (X : set ℝ) : subalgebra ℝ C(X, ℝ) := sorry

theorem weierstrass (a b : ℝ) : (polynomial_subalgebra (set.Icc a b)).topological_closure = ⊤ :=
sorry

theorem abs_mem_closure (X : set ℝ) [compact X]
