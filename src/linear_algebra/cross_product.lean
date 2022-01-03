/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/

import linear_algebra.bilinear_map
import linear_algebra.matrix.determinant
import linear_algebra.vectors

/-!
# Cross products

This module defines the cross product of vectors in $R^3$ for $R$ a commutative ring.

## Main definitions

* `cross_product` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`
* `jacobi_identity`

## Notation

The locale `vectors` gives the following notation:

* `×₃` for the cross product

## Tags

crossproduct
-/

open_locale vectors

variables {R : Type*} [comm_ring R]

/-- The cross product of two vectors in $R^3$ for $R$ a commutative ring. -/
def cross_product : (fin 3 → R) →ₗ[R] (fin 3 → R) →ₗ[R] (fin 3 → R) :=
begin
  apply linear_map.mk₂ R (λ (a b : fin 3 → R),
    ![ (a 1)*(b 2) - (a 2)*(b 1) ,
       (a 2)*(b 0) - (a 0)*(b 2) ,
       (a 0)*(b 1) - (a 1)*(b 0) ]);
  intros;
  simp only [vec3_add,
    pi.add_apply, smul_eq_mul, matrix.smul_cons, matrix.smul_empty, pi.smul_apply];
  apply vec3_eq;
  ring,
end

localized "infixl ` ×₃ `: 68 := cross_product" in vectors

lemma cross_product_apply (a b : fin 3 → R) :
  a ×₃ b =
    ![ (a 1)*(b 2) - (a 2)*(b 1) ,
       (a 2)*(b 0) - (a 0)*(b 2) ,
       (a 0)*(b 1) - (a 1)*(b 0) ] :=
rfl

lemma cross_product_anticomm (v w : fin 3 → R) :
  - (v ×₃ w) = w ×₃ v :=
by simp [cross_product_apply, mul_comm]

lemma cross_product_anticomm' (v w : fin 3 → R) :
  v ×₃ w + w ×₃ v = 0 :=
by rw [add_eq_zero_iff_eq_neg, cross_product_anticomm]

lemma cross_product_self (v : fin 3 → R) :
  v ×₃ v = 0 :=
by simp [cross_product_apply, mul_comm]

/-- The cross product of two vectors is perpendicular to the first vector. -/
lemma dot_self_cross_product (v w : fin 3 → R) :
  v ⬝ (v ×₃ w) = 0 :=
by simp [cross_product_apply, vec3_dot_product, mul_sub, mul_assoc, mul_left_comm]

/-- The cross product of two vectors is perpendicular to the second vector. -/
lemma dot_cross_product_self (v w : fin 3 → R) :
  w ⬝ (v ×₃ w) = 0 :=
by rw [← cross_product_anticomm, matrix.dot_product_neg, dot_self_cross_product, neg_zero]

/-- Cyclic permutations preserve the triple product. See also `triple_product_eq_det`. -/
lemma triple_product_permutation (u v w : fin 3 → R) :
  u ⬝ (v ×₃ w) = v ⬝ (w ×₃ u) :=
begin
  simp only [cross_product_apply, vec3_dot_product,
    matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.empty_append, matrix.cons_val_one,
    matrix.cons_vec_alt0, matrix.cons_append, matrix.cons_val_zero],
  ring,
end

/-- The triple product of `u`, `v`, and `w` is equal to the determinant of the matrix
    with those vectors as its rows. -/
theorem triple_product_eq_det (u v w : fin 3 → R) :
  u ⬝ (v ×₃ w) = matrix.det ![u, v, w] :=
begin
  simp only [vec3_dot_product, cross_product_apply, matrix.det_fin_three,
    matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.empty_vec_alt0, matrix.cons_vec_alt0,
    matrix.vec_head_vec_alt0, fin.fin_append_apply_zero, matrix.empty_append, matrix.cons_append,
    matrix.cons_val', matrix.cons_val_one, matrix.cons_val_zero],
  ring,
end

/-- For a cross product of three vectors, their sum over the three even permutations is equal
    to the zero vector. -/
theorem jacobi_identity (u v w : fin 3 → R) :
  u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
begin
  repeat {rw cross_product_apply},
  norm_num,
  ring_nf,
  tauto,
end
