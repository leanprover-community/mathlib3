import analysis.weierstrass

noncomputable theory

namespace pi

variables {I : Type*} {f : I → Type*} (x : Π i, f i) (i : I)

-- Where does this belong?
-- This doesn't work as a `@[simp]` lemma as there is nothing to index on.
lemma pow_apply [∀ i, monoid $ f i] (n : ℕ) : (x^n) i = (x i)^n :=
begin
  induction n with n ih,
  { simp, },
  { simp [pow_succ, ih], },
end

end pi

namespace continuous_map

open_locale topological_space

variables {X : Type*}

variables [topological_space X] [compact_space X]
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

lemma apply_le_norm (f : C(X, ℝ)) (x : X) : f x ≤ ∥f∥ :=
begin
  -- transitivity,
  -- swap,
  -- apply bounded_continuous_function.norm_coe_le_norm f x,
  sorry,
end
lemma neg_norm_le_apply (f : C(X, ℝ)) (x : X) : -∥f∥ ≤ f x := sorry

def attach_bound (f : C(X, ℝ)) : C(X, set.Icc (-∥f∥) (∥f∥)) :=
{ to_fun := λ x, ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩ }

@[simp] lemma attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attach_bound f) x : ℝ) = f x := rfl

attribute [simp] polynomial.aeval_monomial



@[simp] lemma polynomial.aeval_fn_apply (g : polynomial ℝ)
  (f : X → ℝ)
  (x : X) :
  ((polynomial.aeval f) g) x = g.eval (f x) :=
begin
  apply polynomial.induction_on' g,
  { intros p q hp hq, simp [hp, hq], },
  { intros n a, simp [pi.pow_apply f x n], },
end

@[simp] lemma polynomial.aeval_continuous_map_apply (g : polynomial ℝ)
  (f : C(X, ℝ))
  (x : X) :
  ((polynomial.aeval f) g) x = g.eval (f x) :=
begin
  apply polynomial.induction_on' g,
  { intros p q hp hq, simp [hp, hq], },
  { intros n a, simp [pi.pow_apply f x n], },
end

@[simp, norm_cast] lemma polynomial.aeval_subalgebra_coe
  (g : polynomial R) {A : Type*} [semiring A] [algebra R A] (s : subalgebra R A) (f : s) :
  (polynomial.aeval f g : A) = polynomial.aeval (f : A) g :=
begin
  apply polynomial.induction_on' g,
  { intros p q hp hq, simp [hp, hq], },
  { intros n a, simp, },
end

lemma polynomial_comp_attach_bound (A : subalgebra ℝ C(X, ℝ)) (f : A) (g : polynomial ℝ) :
  ((polynomial.as_continuous_map (set.Icc (-∥f∥) ∥f∥)) g).comp (f : C(X, ℝ)).attach_bound =
    polynomial.aeval f g :=
by { ext, simp, }

/--
Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `set.Icc (-∥f∥) ∥f∥)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
lemma polynomial_comp_attach_bound_mem (A : subalgebra ℝ C(X, ℝ)) (f : A) (g : polynomial ℝ) :
  ((polynomial.as_continuous_map (set.Icc (-∥f∥) ∥f∥)) g).comp (f : C(X, ℝ)).attach_bound ∈ A :=
begin
  rw polynomial_comp_attach_bound,
  apply submodule.coe_mem,
end

theorem comp_attach_bound_mem_closure (A : subalgebra ℝ C(X, ℝ)) (f : A) (p : C(set.Icc (-∥f∥) (∥f∥), ℝ)) :
  p.comp (attach_bound f) ∈ A.topological_closure :=
begin
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p ∈ (polynomial_functions (set.Icc (-∥f∥) (∥f∥))).topological_closure :=
    mem_polynomial_functions_closure _ _ p,
  -- and so there are polynomials arbitrarily close.
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure,
  -- To prove `p.comp (attached_bound f)` is in the closure of polynomials,
  -- we show there are polynomials arbitrarily close.
  apply mem_closure_iff_frequently.mpr,
  -- To show that, we pull back the polynomials close to `p`,
  refine ((pullback_as_continuous_map (attach_bound (f : C(X, ℝ)))).continuous_at p).tendsto
    .frequently_map _ _ frequently_mem_polynomials,
  -- but need to show that those pullbacks are actually in `A`.
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
  apply comp_attach_bound_mem_closure,
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
