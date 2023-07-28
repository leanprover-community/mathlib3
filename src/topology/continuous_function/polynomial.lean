/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.algebra.polynomial
import topology.continuous_function.algebra
import topology.unit_interval

/-!
# Constructions relating polynomial functions and continuous functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `polynomial.to_continuous_map_on p X`: for `X : set R`, interprets a polynomial `p`
  as a bundled continuous function in `C(X, R)`.
* `polynomial.to_continuous_map_on_alg_hom`: the same, as an `R`-algebra homomorphism.
* `polynomial_functions (X : set R) : subalgebra R C(X, R)`: polynomial functions as a subalgebra.
* `polynomial_functions_separates_points (X : set R) : (polynomial_functions X).separates_points`:
  the polynomial functions separate points.

-/

variables {R : Type*}

open_locale polynomial
namespace polynomial


section
variables [semiring R] [topological_space R] [topological_semiring R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
def to_continuous_map (p : R[X]) : C(R, R) :=
⟨λ x : R, p.eval x, by continuity⟩

/--
A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
def to_continuous_map_on (p : R[X]) (X : set R) : C(X, R) :=
⟨λ x : X, p.to_continuous_map x, by continuity⟩

-- TODO some lemmas about when `to_continuous_map_on` is injective?

end

section
variables {α : Type*} [topological_space α]
  [comm_semiring R] [topological_space R] [topological_semiring R]

@[simp] lemma aeval_continuous_map_apply (g : R[X]) (f : C(α, R)) (x : α) :
  ((polynomial.aeval f) g) x = g.eval (f x) :=
begin
  apply polynomial.induction_on' g,
  { intros p q hp hq, simp [hp, hq], },
  { intros n a, simp [pi.pow_apply], },
end

end


section

noncomputable theory

variables [comm_semiring R] [topological_space R] [topological_semiring R]

/--
The algebra map from `R[X]` to continuous functions `C(R, R)`.
-/
@[simps]
def to_continuous_map_alg_hom : R[X] →ₐ[R] C(R, R) :=
{ to_fun := λ p, p.to_continuous_map,
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, },
  map_one' := by { ext, simp, },
  map_mul' := by { intros, ext, simp, },
  commutes' := by { intros, ext, simp [algebra.algebra_map_eq_smul_one], }, }

/--
The algebra map from `R[X]` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def to_continuous_map_on_alg_hom (X : set R) : R[X] →ₐ[R] C(X, R)  :=
{ to_fun := λ p, p.to_continuous_map_on X,
  map_zero' := by { ext, simp, },
  map_add' := by { intros, ext, simp, },
  map_one' := by { ext, simp, },
  map_mul' := by { intros, ext, simp, },
  commutes' := by { intros, ext, simp [algebra.algebra_map_eq_smul_one], }, }

end

end polynomial

section
variables [comm_semiring R] [topological_space R] [topological_semiring R]

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological semiring
`R`.
-/
def polynomial_functions (X : set R) : subalgebra R C(X, R) :=
(⊤ : subalgebra R R[X]).map (polynomial.to_continuous_map_on_alg_hom X)

@[simp]
lemma polynomial_functions_coe (X : set R) :
  (polynomial_functions X : set C(X, R)) = set.range (polynomial.to_continuous_map_on_alg_hom X) :=
by { ext, simp [polynomial_functions], }

-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces a normed algebra isomorphism between `polynomial_functions X` and
-- `polynomial_functions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.

lemma polynomial_functions_separates_points (X : set R) :
  (polynomial_functions X).separates_points :=
λ x y h,
begin
  -- We use `polynomial.X`, then clean up.
  refine ⟨_, ⟨⟨_, ⟨⟨polynomial.X, ⟨algebra.mem_top, rfl⟩⟩, rfl⟩⟩, _⟩⟩,
  dsimp, simp only [polynomial.eval_X],
  exact (λ h', h (subtype.ext h')),
end

open_locale unit_interval
open continuous_map

/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
lemma polynomial_functions.comap_comp_right_alg_hom_Icc_homeo_I (a b : ℝ) (h : a < b) :
  (polynomial_functions I).comap
    (comp_right_alg_hom ℝ ℝ (Icc_homeo_I a b h).symm.to_continuous_map) =
    polynomial_functions (set.Icc a b) :=
begin
  ext f,
  fsplit,
  { rintro ⟨p, ⟨-,w⟩⟩,
    rw fun_like.ext_iff at w,
    dsimp at w,
    let q := p.comp ((b - a)⁻¹ • polynomial.X + polynomial.C (-a * (b-a)⁻¹)),
    refine ⟨q, ⟨_, _⟩⟩,
    { simp, },
    { ext x,
      simp only [neg_mul,
        ring_hom.map_neg, ring_hom.map_mul, alg_hom.coe_to_ring_hom,
        polynomial.eval_X, polynomial.eval_neg, polynomial.eval_C, polynomial.eval_smul,
        smul_eq_mul, polynomial.eval_mul, polynomial.eval_add, polynomial.coe_aeval_eq_eval,
        polynomial.eval_comp, polynomial.to_continuous_map_on_alg_hom_apply,
        polynomial.to_continuous_map_on_apply, polynomial.to_continuous_map_apply],
      convert w ⟨_, _⟩; clear w,
      { -- why does `comm_ring.add` appear here!?
        change x = (Icc_homeo_I a b h).symm ⟨_ + _, _⟩,
        ext,
        simp only [Icc_homeo_I_symm_apply_coe, subtype.coe_mk],
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm,
        simp only [mul_add],
        field_simp, ring, },
      { change _ + _ ∈ I,
        rw [mul_comm (b-a)⁻¹, ←neg_mul, ←add_mul, ←sub_eq_add_neg],
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

end
