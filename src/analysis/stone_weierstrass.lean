import algebra.algebra.subalgebra
import topology.algebra.continuous_functions
import topology.algebra.polynomial
import topology.bounded_continuous_function
import tactic.noncomm_ring

noncomputable theory

open continuous_map

section
variables {R : Type*} [linear_ordered_ring R]

@[simp]
lemma sub_le_sub_flip {x y : R} : y - x ≤ x - y ↔ y ≤ x :=
begin
  rw [sub_le_iff_le_add, sub_add_eq_add_sub, le_sub_iff_add_le],
  rw [←two_mul, ←two_mul],
  exact mul_le_mul_left zero_lt_two,
end

end

section
variables {R : Type*} [linear_ordered_field R]

lemma min_eq_half_add_sub_abs_sub {x y : R} : min x y = 2⁻¹ * (x + y - abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring; linarith,
end

lemma max_eq_half_add_add_abs_sub {x y : R} : max x y = 2⁻¹ * (x + y + abs (x - y)) :=
begin
  dsimp [min, max, abs],
  simp only [neg_le_self_iff, if_congr, sub_nonneg, neg_sub],
  split_ifs; ring; linarith,
end
end

variables {X : Type*} {Y : Type*}
/-- A set of functions "separates points"
if for each pair of points there is a function taking different values on them. -/
def separates_points (A : set (X → Y)) : Prop :=
∀ x y : X, x ≠ y → ∃ f ∈ A, (f x : Y) ≠ f y

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

lemma inf_eq (f g : C(X, ℝ)) : f ⊓ g = (2⁻¹ : ℝ) • (f + g - (f - g).abs) :=
ext (λ _, min_eq_half_add_sub_abs_sub)

lemma sup_eq (f g : C(X, ℝ)) : f ⊔ g = (2⁻¹ : ℝ) • (f + g + (f - g).abs) :=
ext (λ _, max_eq_half_add_add_abs_sub)

theorem inf_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A.topological_closure :=
begin
  rw inf_eq,
  refine A.topological_closure.smul_mem
    (A.topological_closure.sub_mem
      (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property)) _) _,
  exact_mod_cast abs_mem_subalgebra_closure A _,
end

theorem sup_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A.topological_closure :=
begin
  rw sup_eq,
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

/--
The algebra map from `polynomial R` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def polynomial.as_continuous_map (X : set R) : polynomial R →ₐ[R] C(X, R) :=
{ to_fun := λ p,
  { to_fun := λ x, polynomial.aeval (x : R) p,
    continuous_to_fun :=
    begin
      change continuous ((λ x, polynomial.aeval x p) ∘ (λ x: X, (x : R))),
      continuity,
    end },
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, },
  map_one' := by { ext, simp, },
  map_mul' := by { intros, ext, simp, },
  commutes' := by { intros, ext, simp [algebra.algebra_map_eq_smul_one], }, }

-- Injective when `X` is infinite, and `[char_zero R]`?

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological ring `R`.
-/
def polynomial_functions (X : set R) : subalgebra R C(X, R) :=
(⊤ : subalgebra R (polynomial R)).map (polynomial.as_continuous_map X)

-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces an normed algebra isomorphism between `polynomial_functions X` and
-- `polynomial_functions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.

lemma polynomial_functions_separates_points (X : set R) :
  (polynomial_functions X).separates_points :=
λ x y h,
begin
  -- Use `polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨polynomial.X, ⟨algebra.mem_top, rfl⟩⟩, rfl⟩⟩, _⟩⟩,
  dsimp, simp only [polynomial.eval_X],
  exact (λ h', h (subtype.ext h')),
end

/--
The Weierstrass approximation theorem:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`
-/
theorem polynomial_functions_closure_eq_top (a b : ℝ) :
  (polynomial_functions (set.Icc a b)).topological_closure = ⊤ :=
begin
  -- deduce from Stone-Weierstrass?
  sorry
end
