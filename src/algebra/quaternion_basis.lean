/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.quaternion
import tactic.ring

/-!
# Basis on a quaternion-like algebra

## Main definitions

* `quaternion_algebra.basis A c₁ c₂`: a basis for a subspace of an `R`-algebra `A` that has the
  same algebra structure as `ℍ[R,c₁,c₂]`.
* `quaternion_algebra.basis.self R`: the canonical basis for `ℍ[R,c₁,c₂]`.
* `quaternion_algebra.basis.comp_hom b f`: transform a basis `b` by an alg_hom `f`.
* `quaternion_algebra.lift`: Define an `alg_hom` out of `ℍ[R,c₁,c₂]` by its action on the basis
  elements `i`, `j`, and `k`. In essence, this is a universal property. Analogous to `complex.lift`,
  but takes a bundled `quaternion_algebra.basis` instead of just a `subtype` as the amount of
  data / proves is non-negligeable.
-/

open_locale quaternion
namespace quaternion_algebra


/-- A quaternion basis contains the information both sufficient and necessary to construct an
`R`-algebra homomorphism from `ℍ[R,c₁,c₂]` to `A`; or equivalently, a surjective
`R`-algebra homomorphism from `ℍ[R,c₁,c₂]` to an `R`-subalgebra of `A`.

Note that for definitional convenience, `k` is provided as a field even though `i_mul_j` fully
determines it. -/
structure basis {R : Type*} (A : Type*) [comm_ring R] [ring A] [algebra R A] (c₁ c₂ : R) :=
(i j k : A)
(i_mul_i : i * i = c₁ • 1)
(j_mul_j : j * j = c₂ • 1)
(i_mul_j : i * j = k)
(j_mul_i : j * i = -k)

variables {R : Type*} {A B : Type*} [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B]
variables {c₁ c₂ : R}

namespace basis

/-- Since `k` is redundant, it is not necessary to show `q₁.k = q₂.k` when showing `q₁ = q₂`. -/
@[ext]
protected lemma ext ⦃q₁ q₂ : basis A c₁ c₂⦄ (hi : q₁.i = q₂.i) (hj : q₁.j = q₂.j) :
  q₁ = q₂ :=
begin
  cases q₁,
  cases q₂,
  congr',
  rw [←q₁_i_mul_j, ←q₂_i_mul_j],
  congr'
end

variables (R)

/-- There is a natural quaternionic basis for the `quaternion_algebra`. -/
@[simps i j k]
protected def self : basis ℍ[R,c₁,c₂] c₁ c₂ :=
{ i := ⟨0, 1, 0, 0⟩,
  i_mul_i := by { ext; simp },
  j := ⟨0, 0, 1, 0⟩,
  j_mul_j := by { ext; simp },
  k := ⟨0, 0, 0, 1⟩,
  i_mul_j := by { ext; simp },
  j_mul_i := by { ext; simp } }

variables {R}

instance : inhabited (basis ℍ[R,c₁,c₂] c₁ c₂) := ⟨basis.self R⟩

variables (q : basis A c₁ c₂)
include q

attribute [simp] i_mul_i j_mul_j i_mul_j j_mul_i

@[simp] lemma i_mul_k : q.i * q.k = c₁ • q.j :=
by rw [←i_mul_j, ←mul_assoc, i_mul_i, smul_mul_assoc, one_mul]

@[simp] lemma k_mul_i : q.k * q.i = -c₁ • q.j :=
by rw [←i_mul_j, mul_assoc, j_mul_i, mul_neg_eq_neg_mul_symm, i_mul_k, neg_smul]

@[simp] lemma k_mul_j : q.k * q.j = c₂ • q.i :=
by rw [←i_mul_j, mul_assoc, j_mul_j, mul_smul_comm, mul_one]

@[simp] lemma j_mul_k : q.j * q.k = -c₂ • q.i :=
by rw [←i_mul_j, ←mul_assoc, j_mul_i, neg_mul_eq_neg_mul_symm, k_mul_j, neg_smul]

@[simp] lemma k_mul_k : q.k * q.k = -((c₁ * c₂) • 1) :=
by rw [←i_mul_j, mul_assoc, ←mul_assoc q.j _ _, j_mul_i, ←i_mul_j,
  ←mul_assoc, mul_neg_eq_neg_mul_symm, ←mul_assoc, i_mul_i, smul_mul_assoc, one_mul,
  neg_mul_eq_neg_mul_symm, smul_mul_assoc, j_mul_j, smul_smul]

/-- Intermediate result used to define `quaternion_algebra.basis.lift_hom`. -/
def lift (x : ℍ[R,c₁,c₂]) : A :=
algebra_map R _ x.re + x.im_i • q.i + x.im_j • q.j + x.im_k • q.k

lemma lift_zero : q.lift (0 : ℍ[R,c₁,c₂]) = 0 := by simp [lift]
lemma lift_one : q.lift (1 : ℍ[R,c₁,c₂]) = 1 := by simp [lift]
lemma lift_add (x y : ℍ[R,c₁,c₂]) : q.lift (x + y) = q.lift x + q.lift y :=
by { simp [lift, add_smul], abel }
lemma lift_mul (x y : ℍ[R,c₁,c₂]) : q.lift (x * y) = q.lift x * q.lift y :=
begin
  simp only [lift, algebra.algebra_map_eq_smul_one],
  simp only [add_mul],
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    ←algebra.smul_def, smul_add, smul_smul],
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k],
  simp only [smul_smul, smul_neg, sub_eq_add_neg, add_smul, ←add_assoc, mul_neg_eq_neg_mul_symm,
    neg_smul],
  simp only [mul_right_comm _ _ (c₁ * c₂), mul_comm _ (c₁ * c₂)],
  simp only [mul_comm _ c₁, mul_right_comm _ _ c₁],
  simp only [mul_comm _ c₂, mul_right_comm _ _ c₂],
  simp only [←mul_comm c₁ c₂, ←mul_assoc],
  simp [sub_eq_add_neg, add_smul, ←add_assoc],
  abel
end

lemma lift_smul (r : R) (x : ℍ[R,c₁,c₂]) : q.lift (r • x) = r • q.lift x :=
by simp [lift, mul_smul, ←algebra.smul_def]

/-- A `quaternion_algebra.basis` implies an `alg_hom` from the quaternions. -/
@[simps]
def lift_hom : ℍ[R,c₁,c₂] →ₐ[R] A :=
alg_hom.mk'
  { to_fun := q.lift,
    map_zero' := q.lift_zero,
    map_one' := q.lift_one,
    map_add' := q.lift_add,
    map_mul' := q.lift_mul }
  q.lift_smul

/-- Transform a `quaternion_algebra.basis` through an `alg_hom`. -/
@[simps i j k]
def comp_hom (F : A →ₐ[R] B) : basis B c₁ c₂ :=
{ i := F q.i,
  i_mul_i := by rw [←F.map_mul, q.i_mul_i, F.map_smul, F.map_one],
  j := F q.j,
  j_mul_j := by rw [←F.map_mul, q.j_mul_j, F.map_smul, F.map_one],
  k := F q.k,
  i_mul_j := by rw [←F.map_mul, q.i_mul_j],
  j_mul_i := by rw [←F.map_mul, q.j_mul_i, F.map_neg], }

end basis

/-- A quaternionic basis on `A` is equivalent to a map from the quaternion algebra to `A`. -/
@[simps]
def lift : basis A c₁ c₂ ≃ (ℍ[R,c₁,c₂] →ₐ[R] A) :=
{ to_fun := basis.lift_hom,
  inv_fun := (basis.self R).comp_hom,
  left_inv := λ q, begin
    ext;
    simp [basis.lift],
  end,
  right_inv := λ F, begin
    ext,
    dsimp [basis.lift],
    rw ←F.commutes,
    simp only [←F.commutes, ←F.map_smul, ←F.map_add, mk_add_mk, smul_mk, smul_zero, algebra_map_eq],
    congr,
    simp,
  end }

end quaternion_algebra
