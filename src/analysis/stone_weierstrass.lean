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



namespace continuous_map
variables {α : Type*} [topological_space α]
variables {β : Type*} [topological_space β]

instance partial_order [partial_order β] :
  partial_order C(α, β) :=
partial_order.lift (forget_continuity α β) (forget_continuity_injective α β)

lemma le_iff [partial_order β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
iff.refl _

instance has_sup [linear_order β] [order_closed_topology β] : has_sup C(α, β) :=
{ sup := λ f g, { to_fun := λ a, max (f a) (g a), } }

@[simp] lemma sup_apply [linear_order β] [order_closed_topology β] (f g : C(α, β)) (a : α) :
  (f ⊔ g) a = max (f a) (g a) :=
rfl

instance [linear_order β] [order_closed_topology β] : semilattice_sup C(α, β) :=
{ le_sup_left := λ f g, le_iff.mpr (by simp [le_refl]),
  le_sup_right := λ f g, le_iff.mpr (by simp [le_refl]),
  sup_le := λ f₁ f₂ g w₁ w₂, le_iff.mpr (λ a, by simp [le_iff.mp w₁ a, le_iff.mp w₂ a]),
  ..continuous_map.partial_order,
  ..continuous_map.has_sup, }

instance has_inf [linear_order β] [order_closed_topology β] : has_inf C(α, β) :=
{ inf := λ f g, { to_fun := λ a, min (f a) (g a), } }

@[simp] lemma inf_apply [linear_order β] [order_closed_topology β] (f g : C(α, β)) (a : α) :
  (f ⊓ g) a = min (f a) (g a) :=
rfl

instance [linear_order β] [order_closed_topology β] : semilattice_inf C(α, β) :=
{ inf_le_left := λ f g, le_iff.mpr (by simp [le_refl]),
  inf_le_right := λ f g, le_iff.mpr (by simp [le_refl]),
  le_inf := λ f₁ f₂ g w₁ w₂, le_iff.mpr (λ a, by simp [le_iff.mp w₁ a, le_iff.mp w₂ a]),
  ..continuous_map.partial_order,
  ..continuous_map.has_inf, }

instance [linear_order β] [order_closed_topology β] : lattice C(α, β) :=
{ ..continuous_map.semilattice_inf,
  ..continuous_map.semilattice_sup }

end continuous_map

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
