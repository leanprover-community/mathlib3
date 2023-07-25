/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/

import data.matrix.notation
import linear_algebra.bilinear_map
import linear_algebra.matrix.determinant
import algebra.lie.basic

/-!
# Cross products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines the cross product of vectors in $R^3$ for $R$ a commutative ring,
as a bilinear map.

## Main definitions

* `cross_product` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`
* `cross_dot_cross`
* `jacobi_cross`

## Notation

The locale `matrix` gives the following notation:

* `×₃` for the cross product

## Tags

crossproduct
-/

open matrix
open_locale matrix

variables {R : Type*} [comm_ring R]

/-- The cross product of two vectors in $R^3$ for $R$ a commutative ring. -/
def cross_product : (fin 3 → R) →ₗ[R] (fin 3 → R) →ₗ[R] (fin 3 → R) :=
begin
  apply linear_map.mk₂ R (λ (a b : fin 3 → R),
    ![a 1 * b 2 - a 2 * b 1,
      a 2 * b 0 - a 0 * b 2,
      a 0 * b 1 - a 1 * b 0]),
  { intros,
    simp [vec3_add (_ : R), add_comm, add_assoc, add_left_comm, add_mul, sub_eq_add_neg] },
  { intros,
    simp [smul_vec3 (_ : R) (_ : R), mul_comm, mul_assoc, mul_left_comm, mul_add, sub_eq_add_neg] },
  { intros,
    simp [vec3_add (_ : R), add_comm, add_assoc, add_left_comm, mul_add, sub_eq_add_neg] },
  { intros,
    simp [smul_vec3 (_ : R) (_ : R), mul_comm, mul_assoc, mul_left_comm, mul_add, sub_eq_add_neg] },
end

localized "infixl (name := cross_product) ` ×₃ `: 74 := cross_product" in matrix

lemma cross_apply (a b : fin 3 → R) :
  a ×₃ b = ![a 1 * b 2 - a 2 * b 1,
             a 2 * b 0 - a 0 * b 2,
             a 0 * b 1 - a 1 * b 0] :=
rfl

section products_properties

@[simp] lemma cross_anticomm (v w : fin 3 → R) :
  - (v ×₃ w) = w ×₃ v :=
by simp [cross_apply, mul_comm]
alias cross_anticomm ← neg_cross

@[simp] lemma cross_anticomm' (v w : fin 3 → R) :
  v ×₃ w + w ×₃ v = 0 :=
by rw [add_eq_zero_iff_eq_neg, cross_anticomm]

@[simp] lemma cross_self (v : fin 3 → R) :
  v ×₃ v = 0 :=
by simp [cross_apply, mul_comm]

/-- The cross product of two vectors is perpendicular to the first vector. -/
@[simp] lemma dot_self_cross (v w : fin 3 → R) :
  v ⬝ᵥ (v ×₃ w) = 0 :=
by simp [cross_apply, vec3_dot_product, mul_sub, mul_assoc, mul_left_comm]

/-- The cross product of two vectors is perpendicular to the second vector. -/
@[simp] lemma dot_cross_self (v w : fin 3 → R) :
  w ⬝ᵥ (v ×₃ w) = 0 :=
by rw [← cross_anticomm, matrix.dot_product_neg, dot_self_cross, neg_zero]

/-- Cyclic permutations preserve the triple product. See also `triple_product_eq_det`. -/
lemma triple_product_permutation (u v w : fin 3 → R) :
  u ⬝ᵥ (v ×₃ w) = v ⬝ᵥ (w ×₃ u) :=
begin
  simp only [cross_apply, vec3_dot_product,
    matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.empty_vec_append, matrix.cons_val_one,
    matrix.cons_vec_alt0, matrix.cons_vec_append, matrix.cons_val_zero],
  ring,
end

/-- The triple product of `u`, `v`, and `w` is equal to the determinant of the matrix
    with those vectors as its rows. -/
theorem triple_product_eq_det (u v w : fin 3 → R) :
  u ⬝ᵥ (v ×₃ w) = matrix.det ![u, v, w] :=
begin
  simp only [vec3_dot_product, cross_apply, matrix.det_fin_three,
    matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.empty_vec_alt0, matrix.cons_vec_alt0,
    matrix.vec_head_vec_alt0, matrix.vec_append_apply_zero, matrix.empty_vec_append,
    matrix.cons_vec_append, matrix.cons_val', matrix.cons_val_one, matrix.cons_val_zero],
  ring,
end

/-- The scalar quadruple product identity, related to the Binet-Cauchy identity. -/
theorem cross_dot_cross (u v w x : fin 3 → R) :
  (u ×₃ v) ⬝ᵥ (w ×₃ x) = (u ⬝ᵥ w) * (v ⬝ᵥ x) - (u ⬝ᵥ x) * (v ⬝ᵥ w) :=
begin
  simp only [vec3_dot_product, cross_apply, cons_vec_append, cons_vec_bit0_eq_alt0,
    cons_val_one, cons_vec_alt0, linear_map.mk₂_apply, cons_val_zero, head_cons, empty_vec_append],
  ring_nf,
end

end products_properties

section leibniz_properties

/-- The cross product satisfies the Leibniz lie property. -/
lemma leibniz_cross (u v w : fin 3 → R) :
  u ×₃ (v ×₃ w) = (u ×₃ v) ×₃ w + v ×₃ (u ×₃ w) :=
begin
  dsimp only [cross_apply],
  ext i,
  fin_cases i; norm_num; ring,
end

/-- The three-dimensional vectors together with the operations + and ×₃ form a Lie ring.
    Note we do not make this an instance as a conflicting one already exists
    via `lie_ring.of_associative_ring`. -/
def cross.lie_ring : lie_ring (fin 3 → R) :=
{ bracket := λ u v, u ×₃ v,
  add_lie := linear_map.map_add₂ _,
  lie_add := λ u, linear_map.map_add _,
  lie_self := cross_self,
  leibniz_lie := leibniz_cross,
  ..pi.add_comm_group }

local attribute [instance] cross.lie_ring

lemma cross_cross (u v w : fin 3 → R) :
  (u ×₃ v) ×₃ w = u ×₃ (v ×₃ w) - v ×₃ (u ×₃ w) :=
lie_lie u v w

/-- Jacobi identity: For a cross product of three vectors,
    their sum over the three even permutations is equal to the zero vector. -/
theorem jacobi_cross (u v w : fin 3 → R) :
  u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
lie_jacobi u v w

end leibniz_properties
