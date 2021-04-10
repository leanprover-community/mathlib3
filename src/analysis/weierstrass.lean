/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.subalgebra
import topology.algebra.polynomial
import topology.continuous_function.bounded
import analysis.special_functions.bernstein

/-!
# The Weierstrass approximation theorem for continuous functions on `[a,b]`

We've already proved the Weierstrass approximation theorem
in the sense that we've shown that the Bernstein approximations
to a continuous function on `[0,1]` converge uniformly.

Here we rephrase this more abstractly as
`polynomial_functions_closure_eq_top' : (polynomial_functions I).topological_closure = ⊤`
and then, by precomposing with suitable affine functions,
`polynomial_functions_closure_eq_top : (polynomial_functions (set.Icc a b)).topological_closure = ⊤`
-/

noncomputable theory

open continuous_map

variables {X : Type*} [topological_space X]
variables {R : Type*} [comm_ring R] [topological_space R] [topological_ring R]

open filter
open_locale topological_space unit_interval

/--
A set is equivalent to its image under an equivalence.
-/
-- We could construct this using `equiv.set.image e s e.injective`,
-- but this definition provides an explicit inverse.
@[simps]
def equiv.image {α β : Type*} (e : α ≃ β) (s : set α) : s ≃ e '' s :=
{ to_fun := λ x, ⟨e x.1, by simp⟩,
  inv_fun := λ y, ⟨e.symm y.1, by { rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩, simpa using m, }⟩,
  left_inv := λ x, by simp,
  right_inv := λ y, by simp, }.

@[continuity]
lemma homeomorph.continuous_symm {α β : Type*} [topological_space α] [topological_space β]
  (e : α ≃ₜ β) : continuous (e.symm) :=
by continuity

/--
A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
def homeomorph.image {α β : Type*} [topological_space α] [topological_space β]
  (e : α ≃ₜ β) (s : set α) : s ≃ₜ e '' s :=
{ continuous_to_fun := by continuity!,
  continuous_inv_fun := by continuity!,
  ..e.to_equiv.image s, }

/--
The forward direction of a homeomorphism, as a bundled continuous map.
-/
@[simps]
def homeomorph.to_continuous_map {α β : Type*} [topological_space α] [topological_space β]
  (e : α ≃ₜ β) : C(α, β) := ⟨e⟩


/--
The special case of the Weierstrass approximation theorem for the interval `[0,1]`.
This is just a matter of unravelling definitions and using the Bernstein approximations.
-/
theorem polynomial_functions_closure_eq_top' :
  (polynomial_functions I).topological_closure = ⊤ :=
begin
  apply eq_top_iff.mpr,
  rintros f -,
  refine filter.frequently.mem_closure _,
  refine filter.tendsto.frequently (bernstein_approximation_uniform f) _,
  apply frequently_of_forall,
  intro n,
  simp only [subalgebra.mem_coe],
  apply subalgebra.sum_mem,
  rintro n -,
  apply subalgebra.smul_mem,
  dsimp [bernstein, polynomial_functions],
  simp,
end

section
variables {𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affine_homeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 :=
{ to_fun := λ x, a * x + b,
  inv_fun := λ y, (y - b) / a,
  left_inv := λ x, by { simp only [add_sub_cancel], exact mul_div_cancel_left x h, },
  right_inv := λ y, by { simp [mul_div_cancel' _ h], }, }

-- FIXME should be generated directly by `@[simps]`.
-- See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/How.20do.20I.20configure.20an.20.60equiv.60.20to.20work.20with.20.60simps.60.3F/near/233291764
@[simp] lemma affine_homeomorph_apply (a b : 𝕜) (h : a ≠ 0) (x : 𝕜) :
  affine_homeomorph a b h x = a * x + b := rfl

@[simp] lemma affine_homeomorph_symm_apply (a b : 𝕜) (h : a ≠ 0) (y : 𝕜) :
  (affine_homeomorph a b h).symm y = (y - b) / a := rfl

end

section
variables {𝕜 : Type*} [linear_ordered_field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The image of `[0,1]` under the homeomorphism `λ x, a * x + b` is `[b, a+b]`.
-/
-- We only need the ordering on `𝕜` here to avoid talking about flipping the interval over.
@[simp]
lemma affine_homeomorph_image_I (a b : 𝕜) (h : 0 < a) (w) :
  affine_homeomorph a b w '' set.Icc 0 1 = set.Icc b (a + b) :=
begin
  ext,
  fsplit,
  { rintro ⟨x, ⟨⟨zero_le, le_one⟩, rfl⟩⟩,
    simp only [add_le_add_iff_right, affine_homeomorph_apply, le_add_iff_nonneg_left, set.mem_Icc],
    exact ⟨mul_nonneg h.le zero_le, (mul_le_iff_le_one_right h).mpr le_one⟩, },
  { intro m,
    simp only [set.image_congr, set.mem_image, affine_homeomorph_apply],
    use (x - b) / a,
    fsplit,
    { simp only [set.mem_Icc],
      fsplit,
      { apply div_nonneg,
        apply sub_nonneg.mpr,
        exact m.1,
        exact h.le, },
      { apply (div_le_one _).mpr,
        apply sub_le_iff_le_add.mpr,
        exact m.2,
        exact h, } },
    { rw mul_div_cancel' _ w,
      simp, } },
end

/--
The affine homeomorphism from a nontrivial interval `[a,b]` to `[0,1]`.
-/
def Icc_homeo (a b : 𝕜) (h : a < b) : set.Icc a b ≃ₜ set.Icc (0 : 𝕜) (1 : 𝕜) :=
begin
  let e := homeomorph.image (affine_homeomorph (b-a) a (sub_pos.mpr h).ne.symm) (set.Icc 0 1),
  refine (e.trans _).symm,
  apply homeomorph.set_congr,
  rw affine_homeomorph_image_I _ _ (sub_pos.mpr h),
  rw sub_add_cancel,
end

@[simp] lemma Icc_homeo_apply_coe (a b : 𝕜) (h : a < b) (x : set.Icc a b) :
  ((Icc_homeo a b h) x : 𝕜) = (x - a) / (b - a) :=
rfl

@[simp] lemma Icc_homeo_symm_apply_coe (a b : 𝕜) (h : a < b) (x : set.Icc (0 : 𝕜) (1 : 𝕜)) :
  ((Icc_homeo a b h).symm x : 𝕜) = (b - a) * x + a :=
rfl

end


/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
lemma polynomial_functions.comap'_comp_right_alg_hom_Icc_homeo (a b : ℝ) (h : a < b) :
  (polynomial_functions I).comap' (comp_right_alg_hom ℝ (Icc_homeo a b h).symm.to_continuous_map) =
    polynomial_functions (set.Icc a b) :=
begin
  ext f,
  fsplit,
  { rintro ⟨p, ⟨-,w⟩⟩,
    rw continuous_map.ext_iff at w,
    dsimp at w,
    let q := p.comp ((b - a)⁻¹ • polynomial.X + polynomial.C (-a * (b-a)⁻¹)),
    refine ⟨q, ⟨_, _⟩⟩,
    { simp, },
    { ext x,
      simp only [neg_mul_eq_neg_mul_symm,
        ring_hom.map_neg, ring_hom.map_mul, alg_hom.coe_to_ring_hom,
        polynomial.eval_X, polynomial.eval_neg, polynomial.eval_C, polynomial.eval_smul,
        polynomial.eval_mul, polynomial.eval_add, polynomial.coe_aeval_eq_eval,
        polynomial.eval_comp, polynomial.as_continuous_map_on_alg_hom_apply,
        polynomial.as_continuous_map_on_to_fun, polynomial.as_continuous_map_to_fun],
      convert w ⟨_, _⟩; clear w,
      { -- FIXME why does `comm_ring.add` appear here?
        change x = (Icc_homeo a b h).symm ⟨_ + _, _⟩,
        ext,
        simp only [Icc_homeo_symm_apply_coe, subtype.coe_mk],
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm,
        simp only [mul_add],
        field_simp, ring, },
      { change _ + _ ∈ I,
        rw [mul_comm (b-a)⁻¹, ←neg_mul_eq_neg_mul_symm, ←add_mul, ←sub_eq_add_neg],
        have w₁ : 0 < (b-a)⁻¹ := inv_pos.mpr (sub_pos.mpr h),
        have w₂ : 0 ≤ (x : ℝ) - a := sub_nonneg.mpr x.2.1,
        have w₃ : (x : ℝ) - a ≤ b - a := sub_le_sub_right x.2.2 a,
        fsplit,
        { exact mul_nonneg w₂ (le_of_lt w₁), },
        { rw [←div_eq_mul_inv, div_le_one (sub_pos.mpr h)],
          exact w₃, }, }, }, },
  { rintro ⟨p, ⟨-,rfl⟩⟩,
    let q := p.comp ((b - a) • polynomial.X + polynomial.C a),
    refine ⟨q, ⟨_, _⟩⟩,
    { simp, },
    { ext x, simp [mul_comm], }, },
end

lemma continuous_map.subsingleton_subalgebra_ext [subsingleton X] (s₁ s₂ : subalgebra R C(X, R)) :
  s₁ = s₂ :=
begin
  by_cases n : nonempty X,
  { obtain ⟨x⟩ := n,
    ext f,
    have h : f = algebra_map R C(X, R) (f x),
    { ext x', simp only [mul_one, algebra.id.smul_eq_mul, algebra_map_apply], congr, },
    rw h,
    simp only [subalgebra.algebra_map_mem], },
  { ext f,
    have h : f = 0,
    { ext x', exact false.elim (n ⟨x'⟩), },
    subst h,
    simp only [subalgebra.zero_mem], },
end

/--
The Weierstrass approximation theorem:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`

(While we could deduce this as an application of the Stone-Weierstrass theorem,
our proof of that relies on the fact that `abs` is in the closure of polynomials on `[-M, M]`,
so we may as well get this done first.)
-/
theorem polynomial_functions_closure_eq_top (a b : ℝ) :
  (polynomial_functions (set.Icc a b)).topological_closure = ⊤ :=
begin
  by_cases h : a < b, -- (Otherwise it's easy; we'll deal with that later.)
  { -- We can pullback continuous functions to `[a,b]` to continuous functions on `[0,1]`,
    -- by precomposing with an affine map.
    let W : C(set.Icc a b, ℝ) →ₐ[ℝ] C(I, ℝ) :=
      comp_right_alg_hom ℝ (Icc_homeo a b h).symm.to_continuous_map,
    -- This operation is itself a homeomorphism
    -- (with respect to the norm topologies on continuous functions).
    let W' : C(set.Icc a b, ℝ) ≃ₜ C(I, ℝ) := comp_right_homeomorph ℝ (Icc_homeo a b h).symm,
    have w : (W : C(set.Icc a b, ℝ) → C(I, ℝ)) = W' := rfl,
    -- Thus we take the statement of the Weierstrass approximation theorem for `[0,1]`,
    have p := polynomial_functions_closure_eq_top',
    -- and pullback both sides, obtaining an equation between subalgebras of `C([a,b], ℝ)`.
    apply_fun (λ s, s.comap' W) at p,
    simp only [algebra.comap_top] at p,
    -- Since the pullback operation is continuous, it commutes with taking `topological_closure`,
    rw subalgebra.topological_closure_comap'_homeomorph _ W W' w at p,
    -- and precomposing with an affine map takes polynomial functions to polynomial functions.
    rw polynomial_functions.comap'_comp_right_alg_hom_Icc_homeo at p,
    -- 🎉
    exact p },
  { -- Otherwise, `b ≤ a`, and the interval is a subsingleton,
    -- so all subalgebras are the same anyway.
    haveI : subsingleton (set.Icc a b) := ⟨λ x y, le_antisymm
      ((x.2.2.trans (not_lt.mp h)).trans y.2.1) ((y.2.2.trans (not_lt.mp h)).trans x.2.1)⟩,
    apply continuous_map.subsingleton_subalgebra_ext, }
end

/--
An alternative statement of Weierstrass' theorem.
Every real-valued continuous function on `[a,b]` is a uniform limit of polynomials.
-/
theorem mem_polynomial_functions_closure (a b : ℝ) (f : C(set.Icc a b, ℝ)) :
  f ∈ (polynomial_functions (set.Icc a b)).topological_closure :=
begin
  rw polynomial_functions_closure_eq_top _ _,
  simp,
end
