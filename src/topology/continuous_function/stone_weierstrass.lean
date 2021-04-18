/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.continuous_function.weierstrass

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact Hausdorff space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

## Future work

Prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/

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

lemma apply_le_norm (f : C(X, ℝ)) (x : X) : f x ≤ ∥f∥ :=
le_trans (le_abs.mpr (or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)

lemma neg_norm_le_apply (f : C(X, ℝ)) (x : X) : -∥f∥ ≤ f x :=
le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs_self (f x)))

section
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

attribute [simp] polynomial.aeval_monomial

@[simp] lemma polynomial.aeval_fn_apply (g : polynomial R) (f : X → R) (x : X) :
  ((polynomial.aeval f) g) x = g.eval (f x) :=
begin
  apply polynomial.induction_on' g,
  { intros p q hp hq, simp [hp, hq], },
  { intros n a, simp [pi.pow_apply f x n], },
end

@[simp] lemma polynomial.aeval_continuous_map_apply (g : polynomial R) (f : C(X, R)) (x : X) :
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

end


lemma compact_space.elim_nhds_subcover {α : Type*} [topological_space α] [compact_space α]
  (U : α → set α) (hU : ∀ x, U x ∈ 𝓝 x) :
  ∃ t : finset α, (⋃ x ∈ t, U x) = ⊤ :=
begin
  obtain ⟨t, -, s⟩ := is_compact.elim_nhds_subcover compact_univ U (λ x m, hU x),
  exact ⟨t, by { rw eq_top_iff, exact s }⟩,
end

-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : subsemilattice_inf_bot`.
lemma finset.inf_mem {α : Type*} [semilattice_inf_top α]
  (s : set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ x y ∈ s, x ⊓ y ∈ s)
  {ι : Type*} (t : finset ι) (p : ι → α) (h : ∀ i, p i ∈ s) :
  t.inf p ∈ s :=
begin
  classical,
  apply finset.cons_induction_on t,
  { exact w₁, },
  { intros a s' nm ih,
    rw finset.inf_cons,
    apply w₂ _ _ (h a) ih, },
end

lemma finset.inf'_mem {α : Type*} [semilattice_inf α]
  (s : set α) (w : ∀ x y ∈ s, x ⊓ y ∈ s)
  {ι : Type*} (t : finset ι) (H : t.nonempty) (p : ι → α) (h : ∀ i, p i ∈ s) :
  t.inf' H p ∈ s :=
begin
  classical,
  revert H,
  apply finset.cons_induction_on t,
  { rintro ⟨-, ⟨⟩⟩, },
  { intros a s' nm ih H,
    by_cases H' : s'.nonempty,
    { rw finset.inf'_cons H',
      apply w _ _ (h a) (ih H'), },
    { have p : s' = ∅ := finset.not_nonempty_iff_eq_empty.mp H',
      subst p,
      simp [h a], }, },
end

lemma finset.sup_mem {α : Type*} [semilattice_sup_bot α]
  (s : set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ x y ∈ s, x ⊔ y ∈ s)
  {ι : Type*} (t : finset ι) (p : ι → α) (h : ∀ i, p i ∈ s) :
  t.sup p ∈ s :=
@finset.inf_mem (order_dual α) _ s w₁ w₂ _ t p h

lemma finset.sup'_mem {α : Type*} [semilattice_sup α]
  (s : set α) (w : ∀ x y ∈ s, x ⊔ y ∈ s)
  {ι : Type*} (t : finset ι) (H : t.nonempty) (p : ι → α) (h : ∀ i, p i ∈ s) :
  t.sup' H p ∈ s :=
@finset.inf'_mem (order_dual α) _ s w _ t H p h

open_locale topological_space

lemma inf'_mem_nhds {α : Type*} [topological_space α]
  {ι : Type*} (t : finset ι) (H : t.nonempty)
  (p : ι → set α) (x : α) (h : ∀ i, i ∈ t → p i ∈ 𝓝 x) :
  t.inf' H p ∈ 𝓝 x :=
begin
  revert H h,
  apply finset.cons_induction_on t,
  { rintro ⟨-, ⟨⟩⟩, },
  { intros a s' nm ih H h,
    by_cases H' : s'.nonempty,
    { rw finset.inf'_cons H',
      simp [h a (by simp), ih H' (λ i m, h i (by simp [m]))], },
    { have p : s' = ∅ := finset.not_nonempty_iff_eq_empty.mp H',
      subst p,
      exact h a (by simp), } }
end

lemma nonempty_of_union_eq_top_of_nonempty
  {α ι : Type*} (t : finset ι) (p : ι → set α) (H : nonempty α) (w : (⋃ i ∈ t, p i) = ⊤) :
  t.nonempty :=
begin
  rw eq_top_iff at w,
  obtain ⟨-, ⟨g,rfl⟩, h⟩ := set.mem_of_mem_of_subset (set.mem_univ H.some) w,
  simp only [exists_prop, set.mem_Union] at h,
  exact ⟨g, h.1⟩,
end

lemma foo (a b ε : ℝ) : dist a b < ε ↔ a < b + ε ∧ b - ε < a :=
begin
  dsimp [dist],
  rw abs_lt,
  refine ⟨λ p, ⟨_, _⟩, λ p, ⟨_, _⟩⟩; cases p; linarith,
end

lemma bar {X : Type*} {xs : finset X} {U : X → set X}
  (w : (⋃ (x : X) (H : x ∈ xs), U x) = ⊤) (z : X) :
  ∃ (x : X), x ∈ xs ∧ z ∈ U x :=
begin
  have p : z ∈ ⊤ := set.mem_univ _,
  rw ←w at p,
  simp_rw [set.mem_Union] at p,
  obtain ⟨x, xm, zm⟩ := p,
  exact ⟨x, xm, zm⟩,
end

-- Everything above this point belongs somewhere else!

/--
Turn a function `f : C(X, ℝ)` into a continuous map into `set.Icc (-∥f∥) (∥f∥)`,
thereby explicitly attaching bounds.
-/
def attach_bound (f : C(X, ℝ)) : C(X, set.Icc (-∥f∥) (∥f∥)) :=
{ to_fun := λ x, ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩ }

@[simp] lemma attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attach_bound f) x : ℝ) = f x := rfl

lemma polynomial_comp_attach_bound (A : subalgebra ℝ C(X, ℝ)) (f : A) (g : polynomial ℝ) :
  (g.to_continuous_map_on (set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attach_bound =
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
  (g.to_continuous_map_on (set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attach_bound ∈ A :=
begin
  rw polynomial_comp_attach_bound,
  apply set_like.coe_mem,
end

theorem comp_attach_bound_mem_closure
  (A : subalgebra ℝ C(X, ℝ)) (f : A) (p : C(set.Icc (-∥f∥) (∥f∥), ℝ)) :
  p.comp (attach_bound f) ∈ A.topological_closure :=
begin
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p ∈ (polynomial_functions (set.Icc (-∥f∥) (∥f∥))).topological_closure :=
    continuous_map_mem_polynomial_functions_closure _ _ p,
  -- and so there are polynomials arbitrarily close.
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure,
  -- To prove `p.comp (attached_bound f)` is in the closure of polynomials,
  -- we show there are polynomials arbitrarily close.
  apply mem_closure_iff_frequently.mpr,
  -- To show that, we pull back the polynomials close to `p`,
  refine ((comp_right_continuous_map ℝ (attach_bound (f : C(X, ℝ)))).continuous_at p).tendsto
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

-- Here's the fun part of Stone-Weierstrass!
theorem sublattice_closure_eq_top
  (L : set C(X, ℝ)) (nA : L.nonempty)
  (inf_mem : ∀ f g ∈ L, f ⊓ g ∈ L) (sup_mem : ∀ f g ∈ L, f ⊔ g ∈ L)
  (sep : L.separates_points_strongly) :
  closure L = ⊤ :=
begin
  -- We start by boiling down to a statement about close approximation.
  apply eq_top_iff.mpr,
  rintros f -,
  refine filter.frequently.mem_closure _,
  refine (filter.has_basis.frequently_iff metric.nhds_basis_ball).mpr _,
  intros ε pos,
  simp only [exists_prop, metric.mem_ball],

  -- It will be helpful to assume `X` is nonempty later,
  -- so we get that out of the way here.
  by_cases nX : nonempty X,
  swap,
  refine ⟨nA.some, (dist_lt_iff _ _ pos).mpr (λ x, false.elim (nX ⟨x⟩)), nA.some_spec⟩,

  /-
  The strategy now is to pick a family of continuous functions `g x y` in `A`
  with the property that `g x y x = f x` and `g x y y = f y`
  (this is immediate from `h : separates_points_strongly`)
  then use continuity to see that `g x y` is close to `f` near both `x` and `y`,
  and finally using compactness to produce the desired function `h`
  as a maximum over finitely many `x` of a minimum over finitely many `y` of the `g x y`.
  -/
  dsimp [set.separates_points_strongly] at sep,

  let g : Π x y, L := λ x y, (sep f x y).some,
  let w₁ : ∀ x y, g x y x = f x := λ x y, (sep f x y).some_spec.1,
  let w₂ : ∀ x y, g x y y = f y := λ x y, (sep f x y).some_spec.2,

  -- For each `x y`, we define `U x y` to be `{ z | f z - ε < g x y z }`,
  -- and observe this is a neighbourhood of `y`.
  let U : Π x y, set X := λ x y, { z | f z - ε < g x y z },
  have U_nhd_y : ∀ x y, U x y ∈ 𝓝 y,
  { intros x y,
    refine mem_nhds_sets _ _,
    { rw [show U x y = (f - g x y : C(X, ℝ)) ⁻¹' set.Iio ε, { ext z, simp [sub_lt], }],
      exact is_open.preimage (by continuity) is_open_Iio, },
    { rw [set.mem_set_of_eq, w₂],
      exact sub_lt_self _ pos, }, },

  -- Fixing `x` for a moment, we have a family of functions `λ y, g x y`
  -- which on different patches (the `U x y`) are greater than `f z - ε`.
  -- Taking the supremum of these functions corresponding to a finite collection of patches
  -- will give us an element of `A` that is globally greater than `f z - ε`.

  -- Since `X` is compact, for every `x` there is some finset `ys t`
  -- so the union of the `U x y` for `y ∈ ys x` still covers everything.
  let ys : Π x, finset X := λ x, (compact_space.elim_nhds_subcover (U x) (U_nhd_y x)).some,
  let ys_w : ∀ x, (⋃ y ∈ ys x, U x y) = ⊤ :=
    λ x, (compact_space.elim_nhds_subcover (U x) (U_nhd_y x)).some_spec,
  have ys_nonempty : ∀ x, (ys x).nonempty :=
    λ x, nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x),

  -- Thus for each `x` we have the desired `h x : A` so `f z - ε < h x z` everywhere.
  let h : Π x, L := λ x,
    ⟨(ys x).sup' (ys_nonempty x) (λ y, (g x y : C(X, ℝ))),
      finset.sup'_mem _ sup_mem _ _ _ (λ y, (g x y).2)⟩,
  have lt_h : ∀ x z, f z - ε < h x z,
  { intros x z,
    obtain ⟨y, ym, zm⟩ := bar (ys_w x) z,
    dsimp [h],
    simp only [finset.lt_sup'_iff, continuous_map.sup'_apply],
    exact ⟨y, ym, zm⟩, },

  -- For each `x y`, we define `V x y` to be `{ z | g x y z < f z + ε }`,
  -- and observe this is a neighbourhood of `x`.
  let V : Π x y, set X := λ x y, { z | g x y z < f z + ε },
  have V_nhd_x : ∀ x y, V x y ∈ 𝓝 x,
  { intros x y,
    refine mem_nhds_sets _ _,
    { rw [show V x y = (g x y - f : C(X, ℝ)) ⁻¹' set.Iio ε, { ext z, simp [sub_lt_iff_lt_add'], }],
      exact is_open.preimage (by continuity) is_open_Iio, },
    { rw [set.mem_set_of_eq, w₁],
      exact (lt_add_iff_pos_right _).mpr pos, }, },

  -- For each `x`, we can take the finite intersection of the `V x y` corresponding to `y ∈ ys x`.
  let W : Π x, set X := λ x, (ys x).inf' (ys_nonempty x) (λ y, V x y),
  -- This is still a neighbourhood of `x`.
  have W_nhd : ∀ x, W x ∈ 𝓝 x := λ x, inf'_mem_nhds _ _ _ _ (λ y m, V_nhd_x x y),
  -- Locally on each `W x`, we have `h x z < f z + ε`, since `h x` is a supremum of the `g x y`.
  have h_lt : ∀ (x) (z ∈ W x), h x z < f z + ε,
  { intros x z zm,
    dsimp [h],
    simp only [continuous_map.sup'_apply, finset.sup'_lt_iff],
    intros y ys,
    have zm' : z ∈ V x y := set.mem_of_mem_of_subset zm (finset.inf'_le (V x) ys),
    exact zm', },

  -- Since `X` is compact, there is some finset `ys t`
  -- so the union of the `W x` for `x ∈ xs` still covers everything.
  let xs : finset X := (compact_space.elim_nhds_subcover W W_nhd).some,
  let xs_w : (⋃ x ∈ xs, W x) = ⊤ :=
    (compact_space.elim_nhds_subcover W W_nhd).some_spec,
  have xs_nonempty : xs.nonempty := nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w,

  -- Finally our candidate function is the infimum over `x ∈ xs` of the `h x`.
  -- This function is then globally less than `f z + ε`.
  let k : (L : Type*) :=
    ⟨xs.inf' xs_nonempty (λ x, (h x : C(X, ℝ))),
      finset.inf'_mem _ inf_mem _ _ _ (λ x, (h x).2)⟩,

  refine ⟨k.1, _, k.2⟩,
  rw dist_lt_iff _ _ pos,
  intro z,
  rw foo,
  fsplit,
  { dsimp [k],
    simp only [finset.inf'_lt_iff, continuous_map.inf'_apply],
    obtain ⟨x, xm, zm⟩ := bar xs_w z,
    exact ⟨x, xm, h_lt _ _ zm⟩, },
  { dsimp [k],
    simp only [finset.lt_inf'_iff, continuous_map.inf'_apply],
    intros x xm,
    apply lt_h, },
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
  let L := A.topological_closure,
  have n : set.nonempty (L : set C(X, ℝ)) :=
    ⟨(1 : C(X, ℝ)), A.subalgebra_topological_closure A.one_mem⟩,
  convert sublattice_closure_eq_top
    (L : set C(X, ℝ)) n
    (λ f g fm gm, inf_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
    (λ f g fm gm, sup_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
    (subalgebra.separates_points.strongly
      (subalgebra.separates_points_monotone (A.subalgebra_topological_closure) w)),
  { simp, },
  { ext, simp, },
end

end continuous_map
