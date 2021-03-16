import algebra.algebra.subalgebra
import topology.algebra.continuous_functions
import topology.instances.real
import topology.algebra.algebra
import topology.algebra.continuous_functions
import topology.algebra.polynomial
import topology.bounded_continuous_function

noncomputable theory

open continuous_map

variables {X : Type*} {Y : Type*}
/-- A set of functions "separates points"
if for each pair of points there is a function taking different values on them. -/
def separates_points (A : set (X → Y)) : Prop :=
∀ x y : X, ∃ f ∈ A, (f x : Y) ≠ f y

variables [topological_space X]
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

abbreviation subalgebra.separates_points (A : subalgebra R C(X, R)) : Prop :=
separates_points ((λ f : C(X, R), (f : X → R)) '' (A : set C(X, R)))

/-- The pointwise absolute value of a continuous function as a continuous function. -/
def continuous_map.abs
  {R : Type*} [linear_ordered_add_comm_group R] [topological_space R] [order_topology R]
  (f : C(X, R)) : C(X, R) :=
{ to_fun := λ x, abs (f x), }

variables [compact_space X]

theorem abs_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f : A) :
  (f : C(X, ℝ)).abs ∈ A.topological_closure :=
begin
  -- rewrite `f.abs` as `abs ∘ f`,
  -- then use that `abs` is in the closure of polynomials on `[-M, M]`,
  -- where `∥f∥ ≤ M`.
  sorry
end

lemma min_eq {x y : ℝ} : min x y = 2⁻¹ * (x + y - abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring; linarith,
end

lemma max_eq {x y : ℝ} : max x y = 2⁻¹ * (x + y + abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring; linarith,
end

lemma min_eq' (f g : C(X, ℝ)) : f ⊓ g = (2⁻¹ : ℝ) • (f + g - (f - g).abs) :=
ext (λ _, min_eq)

lemma max_eq' (f g : C(X, ℝ)) : f ⊔ g = (2⁻¹ : ℝ) • (f + g + (f - g).abs) :=
ext (λ _, max_eq)

theorem inf_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A.topological_closure :=
begin
  rw min_eq',
  refine A.topological_closure.smul_mem
    (A.topological_closure.sub_mem
      (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property)) _) _,
  exact_mod_cast abs_mem_subalgebra_closure A _,
end

theorem sup_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A.topological_closure :=
begin
  rw max_eq',
  refine A.topological_closure.smul_mem
    (A.topological_closure.add_mem
      (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property)) _) _,
  exact_mod_cast abs_mem_subalgebra_closure A _,
end

theorem sublattice_closure_eq_top
  (A : set C(X, ℝ)) (inf_mem : ∀ f g ∈ A, f ⊓ g ∈ A) (sup_mem : ∀ f g ∈ A, f ⊔ g ∈ A)
  (h : separates_points ((λ f : C(X, ℝ), (f : X → ℝ)) '' A)) :
  closure A = ⊤ :=
sorry



variables [t2_space X]

/--
The Stone-Weierstrass approximation theorem,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact Hausdorff space,
is dense if and only if it separates points.
-/
theorem continuous_map.subalgebra_separates_points_iff_topological_closure_eq_top
  (A : subalgebra ℝ C(X, ℝ)) :
  A.topological_closure = ⊤ ↔ A.separates_points :=
sorry


def polynomial_functions (X : set R) : subalgebra R C(X, R) := sorry

lemma polynomial_functions_separates_points (X : set R) :
  (polynomial_functions X).separates_points :=
sorry

/--
The Weierstrass approximation theorem:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`
-/
theorem polynomial_functions_closure_eq_top (a b : ℝ) :
  (polynomial_functions (set.Icc a b)).topological_closure = ⊤ :=
begin
  -- deduce from Stone-Weierstrass
  sorry
end
