import analysis.weierstrass

noncomputable theory

namespace continuous_map

variables {X : Type*}

variables [topological_space X] [compact_space X]
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

theorem abs_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f : A) :
  (f : C(X, ℝ)).abs ∈ A.topological_closure :=
begin
  -- rewrite `f.abs` as `abs ∘ f`,
  -- then use that `abs` is in the closure of polynomials on `[-M, M]`,
  -- where `∥f∥ ≤ M`.
  sorry
end

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

theorem inf_mem_closed_subalgebra (A : subalgebra ℝ C(X, ℝ)) (h : is_closed (A : set C(X, ℝ)))
  (f g : A) : (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A :=
begin
  convert inf_mem_subalgebra_closure A f g,
  apply subalgebra.ext_set,
  symmetry,
  erw closure_eq_iff_is_closed,
  exact h,
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

theorem sup_mem_closed_subalgebra (A : subalgebra ℝ C(X, ℝ)) (h : is_closed (A : set C(X, ℝ)))
  (f g : A) : (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A :=
begin
  convert sup_mem_subalgebra_closure A f g,
  apply subalgebra.ext_set,
  symmetry,
  erw closure_eq_iff_is_closed,
  exact h,
end

theorem sublattice_closure_eq_top
  (A : set C(X, ℝ)) (inf_mem : ∀ f g ∈ A, f ⊓ g ∈ A) (sup_mem : ∀ f g ∈ A, f ⊔ g ∈ A)
  (h : separates_points_strongly ((λ f : C(X, ℝ), (f : X → ℝ)) '' A)) :
  closure A = ⊤ :=
begin
  -- Here's the fun part of Stone-Weierstrass!
  sorry
end

variables [t2_space X]

/--
The Stone-Weierstrass approximation theorem,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact Hausdorff space,
is dense if it separates points.
-/
theorem subalgebra_topological_closure_eq_top_of_separates_points
  (A : subalgebra ℝ C(X, ℝ)) (w : A.separates_points) :
  A.topological_closure = ⊤ :=
begin
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply subalgebra.ext_set,
  let B := A.topological_closure,
  convert sublattice_closure_eq_top
    (B : set C(X, ℝ))
    (λ f g fm gm, inf_mem_closed_subalgebra B A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
    (λ f g fm gm, sup_mem_closed_subalgebra B A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
    (subalgebra.separates_points_strongly
      (subalgebra.separates_points_monotone (A.subalgebra_topological_closure) w)),
  { simp, },
  { ext, simp, sorry, },
end

end continuous_map
