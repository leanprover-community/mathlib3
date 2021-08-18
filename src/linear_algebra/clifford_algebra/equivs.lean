/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.quaternion_basis
import data.complex.module
import linear_algebra.clifford_algebra.basic

/-!
# Other constructions isomorphic to Clifford Algebras

This file contains isomorphisms showing that other types are equivalent to some `clifford_algebra`:

* `clifford_algebra_ring.equiv`: any ring is equivalent to a `clifford_algebra` over a
  zero-dimensional vector space
* `clifford_algebra_complex.equiv`: the `complex` numbers are equivalent to a
  `clifford_algebra` over a one-dimensional vector space with a quadratic form that satisfies
  `Q (ι Q 1) = -1`.
* `clifford_algebra_quaternion.equiv`: a `quaternion_algebra` over `R` is equivalent to a clifford
  algebra over `R × R`, sending `i` to `(0, 1)` and `j` to `(1, 0)`.
-/

open clifford_algebra

/-! ### The clifford algebra isomorphic to a ring -/
namespace clifford_algebra_ring

variables {R : Type*} [comm_ring R]

@[simp]
lemma ι_eq_zero : ι (0 : quadratic_form R unit) = 0 :=
subsingleton.elim _ _

/-- The clifford algebra over a 0-dimensional vector space is isomorphic to its scalars. -/
protected def equiv : clifford_algebra (0 : quadratic_form R unit) ≃ₐ[R] R :=
alg_equiv.of_alg_hom
  (clifford_algebra.lift (0 : quadratic_form R unit) $
    ⟨0, λ m : unit, (zero_mul (0 : R)).trans (algebra_map R _).map_zero.symm⟩)
  (algebra.of_id R _)
  (by { ext x, exact (alg_hom.commutes _ x), })
  (by { ext : 1, rw [ι_eq_zero, linear_map.comp_zero, linear_map.comp_zero], })

end clifford_algebra_ring

/-! ### The clifford algebra isomorphic to the complex numbers -/
namespace clifford_algebra_complex

/-- The quadratic form sending elements to the negation of their square. -/
def Q : quadratic_form ℝ ℝ := -quadratic_form.lin_mul_lin linear_map.id linear_map.id

@[simp]
lemma Q_apply (r : ℝ) : Q r = - (r * r) := rfl

/-- Intermediate result for `clifford_algebra_complex.equiv`: clifford algebras over
`clifford_algebra_complex.Q` above can be converted to `ℂ`. -/
def to_complex : clifford_algebra Q →ₐ[ℝ] ℂ :=
clifford_algebra.lift Q ⟨linear_map.to_span_singleton _ _ complex.I, λ r, begin
  dsimp [linear_map.to_span_singleton, linear_map.id],
  rw smul_mul_smul,
  simp,
end⟩

@[simp]
lemma to_complex_ι (r : ℝ) : to_complex (ι Q r) = r • complex.I :=
clifford_algebra.lift_ι_apply _ _ r

/-- The clifford algebras over `clifford_algebra_complex.Q` is isomorphic as an `ℝ`-algebra to
`ℂ`. -/
@[simps]
protected def equiv : clifford_algebra Q ≃ₐ[ℝ] ℂ :=
alg_equiv.of_alg_hom to_complex
  (complex.lift ⟨clifford_algebra.ι Q 1, begin
    rw [clifford_algebra.ι_sq_scalar, Q_apply, one_mul, ring_hom.map_neg, ring_hom.map_one],
  end⟩)
  (begin
    ext1,
    dsimp only [alg_hom.comp_apply, subtype.coe_mk, alg_hom.id_apply, complex.lift_apply],
    rw [complex.lift_aux_apply_I, to_complex_ι, one_smul],
  end)
  (begin
    ext,
    dsimp only [linear_map.comp_apply, complex.lift_apply, subtype.coe_mk, alg_hom.id_apply,
      alg_hom.to_linear_map_apply, alg_hom.comp_apply],
    rw [to_complex_ι, one_smul, complex.lift_aux_apply_I],
  end)

-- this name is too short for us to want it visible after `open clifford_algebra_complex`
attribute [protected] Q

end clifford_algebra_complex

/-! ### The clifford algebra isomorphic to the quaternions -/
namespace clifford_algebra_quaternion

open_locale quaternion
open quaternion_algebra

variables {R : Type*} [comm_ring R] (c₁ c₂ : R)

/-- `Q c₁ c₂` is a quadratic form over `R × R` such that `clifford_algebra (Q c₁ c₂)` is isomorphic
as an `R`-algebra to `ℍ[R,c₁,c₂]`. -/
def Q : quadratic_form R (R × R) :=
c₁ • quadratic_form.lin_mul_lin (linear_map.fst _ _ _) (linear_map.fst _ _ _) +
c₂ • quadratic_form.lin_mul_lin (linear_map.snd _ _ _) (linear_map.snd _ _ _)

@[simp]
lemma Q_apply (v : R × R) : Q c₁ c₂ v = c₁ * (v.1 * v.1) + c₂ * (v.2 * v.2) := rfl

/-- The quaternion basis vectors within the algebra. -/
@[simps i j k]
def quaternion_basis : quaternion_algebra.basis (clifford_algebra (Q c₁ c₂)) c₁ c₂ :=
{ i := ι (Q c₁ c₂) (1, 0),
  j := ι (Q c₁ c₂) (0, 1),
  k := ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1),
  i_mul_i := begin
    rw [ι_sq_scalar, Q_apply, ←algebra.algebra_map_eq_smul_one],
    simp,
  end,
  j_mul_j := begin
    rw [ι_sq_scalar, Q_apply, ←algebra.algebra_map_eq_smul_one],
    simp,
  end,
  i_mul_j := rfl,
  j_mul_i := begin
    rw [eq_neg_iff_add_eq_zero, ι_mul_ι_add_swap, quadratic_form.polar],
    simp,
  end }

variables {c₁ c₂}

/-- Intermediate result of `clifford_algebra_quaternion.equiv`: clifford algebras over
`clifford_algebra_quaternion.Q` can be converted to `ℍ[R,c₁,c₂]`. -/
def to_quaternion : clifford_algebra (Q c₁ c₂) →ₐ[R] ℍ[R,c₁,c₂] :=
clifford_algebra.lift (Q c₁ c₂) ⟨
  { to_fun := λ v, (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]),
    map_add' := λ v₁ v₂, by simp,
    map_smul' := λ r v, by ext; simp },
  λ v, begin
    dsimp,
    ext,
    all_goals {dsimp, ring},
  end⟩

@[simp]
lemma to_quaternion_ι (v : R × R) :
  to_quaternion (ι (Q c₁ c₂) v) = (⟨0, v.1, v.2, 0⟩ : ℍ[R,c₁,c₂]) :=
clifford_algebra.lift_ι_apply _ _ v

/-- Map a quaternion into the clifford algebra. -/
def of_quaternion : ℍ[R,c₁,c₂] →ₐ[R] clifford_algebra (Q c₁ c₂) :=
(quaternion_basis c₁ c₂).lift_hom

@[simp] lemma of_quaternion_apply (x : ℍ[R,c₁,c₂]) :
  of_quaternion x = algebra_map R _ x.re
                  + x.im_i • ι (Q c₁ c₂) (1, 0)
                  + x.im_j • ι (Q c₁ c₂) (0, 1)
                  + x.im_k • (ι (Q c₁ c₂) (1, 0) * ι (Q c₁ c₂) (0, 1)) := rfl

@[simp]
lemma of_quaternion_comp_to_quaternion :
  of_quaternion.comp to_quaternion = alg_hom.id R (clifford_algebra (Q c₁ c₂)) :=
begin
  ext : 1,
  dsimp, -- before we end up with two goals and have to do this twice
  ext,
  all_goals {
    dsimp,
    rw to_quaternion_ι,
    dsimp,
    simp only [to_quaternion_ι, zero_smul, one_smul, zero_add, add_zero, ring_hom.map_zero], },
end

@[simp]
lemma to_quaternion_comp_of_quaternion :
  to_quaternion.comp of_quaternion = alg_hom.id R ℍ[R,c₁,c₂] :=
begin
  apply quaternion_algebra.lift.symm.injective,
  ext1; dsimp [quaternion_algebra.basis.lift]; simp,
end

/-- The clifford algebra over `clifford_algebra_quaternion.Q c₁ c₂` is isomorphic as an `R`-algebra
to `ℍ[R,c₁,c₂]`. -/
@[simps]
protected def equiv : clifford_algebra (Q c₁ c₂) ≃ₐ[R] ℍ[R,c₁,c₂] :=
alg_equiv.of_alg_hom to_quaternion of_quaternion
  to_quaternion_comp_of_quaternion
  of_quaternion_comp_to_quaternion

-- this name is too short for us to want it visible after `open clifford_algebra_quaternion`
attribute [protected] Q

end clifford_algebra_quaternion
