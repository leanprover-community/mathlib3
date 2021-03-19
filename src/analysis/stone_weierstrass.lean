import analysis.weierstrass

noncomputable theory

namespace continuous_map

open_locale topological_space

lemma frequently_in_nhds_map {X Y : Type*} [topological_space X] [topological_space Y]
  {P : X → Prop} {Q : Y → Prop} {f : X → Y} {p : X} (c : continuous_at f p) (w : ∀ x, P x → Q (f x))
  (h : ∃ᶠ x in nhds p, P x) : ∃ᶠ y in nhds (f p), Q y :=
λ h', h (filter.mem_sets_of_superset (c.preimage_mem_nhds h')
  (λ x nq, (λ np, nq (w x np))))

variables {X : Type*}

variables [topological_space X] [compact_space X]
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

lemma apply_le_norm (f : C(X, ℝ)) (x : X) : f x ≤ ∥f∥ := sorry
lemma neg_norm_le_apply (f : C(X, ℝ)) (x : X) : -∥f∥ ≤ f x := sorry

def attach_bound (f : C(X, ℝ)) : C(X, set.Icc (-∥f∥) (∥f∥)) :=
{ to_fun := λ x, ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩ }

@[simp] lemma attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attach_bound f) x : ℝ) = f x := rfl

lemma polynomial_comp_attach_bound_mem (A : subalgebra ℝ C(X, ℝ)) (f : A) (g : polynomial ℝ) :
  ((polynomial.as_continuous_map (set.Icc (-∥f∥) ∥f∥)) g).comp (f : C(X, ℝ)).attach_bound ∈ A :=
begin
  apply polynomial.induction_on' g,
  { intros p q hp hq,
    simp only [alg_hom.map_add, continuous_map.add_comp],
    exact A.add_mem hp hq, },
  { intros n a,
    rw polynomial.monomial_eq_smul_X,
    simp,
    apply A.smul_mem,
    apply A.pow_mem,
    convert f.2,
    ext, simp, }
end

theorem foo (A : subalgebra ℝ C(X, ℝ)) (f : A) (p : C(set.Icc (-∥f∥) (∥f∥), ℝ)) :
  p.comp (attach_bound f) ∈ A.topological_closure :=
begin
  have : p ∈ (polynomial_functions (set.Icc (-∥f∥) (∥f∥))).topological_closure :=
    mem_polynomial_functions_closure _ _ p,
  have := mem_closure_iff_frequently.mp this,
  apply mem_closure_iff_frequently.mpr,
  apply frequently_in_nhds_map
    ((pullback_as_continuous_map (attach_bound (f : C(X, ℝ)))).continuous_at p) _ this,
  rintros _ ⟨g, ⟨-,rfl⟩⟩,
  simp,
  apply polynomial_comp_attach_bound_mem,
end

theorem abs_mem_subalgebra_closure (A : subalgebra ℝ C(X, ℝ)) (f : A) :
  (f : C(X, ℝ)).abs ∈ A.topological_closure :=
begin
  let M := ∥f∥,
  let f' := attach_bound (f : C(X, ℝ)),
  let abs : C(set.Icc (-∥f∥) (∥f∥), ℝ) :=
  { to_fun := λ x : set.Icc (-∥f∥) (∥f∥), _root_.abs (x : ℝ) },
  change (abs.comp f') ∈ A.topological_closure,
  apply foo,
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
  { ext, simp, },
end

end continuous_map
