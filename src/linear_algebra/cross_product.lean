/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/

import data.matrix.basic
import data.matrix.notation
import linear_algebra.bilinear_map
import linear_algebra.matrix.determinant
import tactic.fin_cases

/-!
# Cross products

This module defines the cross product of vectors in $R^3$ for $R$ a commutive ring.

## Main definitions

* `cross_product` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`

## Notation

The locale `vectors` gives the following notations:

* `×₃` for the cross product
* `⬝`  for dot products

## Tags

crossproduct
-/


variables {R : Type*} [comm_ring R]

private lemma vec3_eq {a b : fin 3 → R} (h₀ : a 0 = b 0) (h₁ : a 1 = b 1) (h₂ : a 2 = b 2) :
  a = b :=
by { ext x, fin_cases x; assumption }

private lemma vec3_eq' {a₀ a₁ a₂ b₀ b₁ b₂ : R} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
  ![a₀, a₁, a₂] = ![b₀, b₁, b₂] :=
by rw [h₀, h₁, h₂]

private lemma vec3_add {a b : fin 3 → R} :
  a + b = ![a 0 + b 0, a 1 + b 1, a 2 + b 2] :=
by { apply vec3_eq; refl }

private lemma vec3_add' {a₀ a₁ a₂ b₀ b₁ b₂ : R} :
  ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] :=
by { rw vec3_add, refl }



/-- The cross product of two vectors in $R^3$ for $R$ a commutative ring. -/
def cross_product : (fin 3 → R) →ₗ[R] (fin 3 → R) →ₗ[R] (fin 3 → R) :=
begin
  apply linear_map.mk₂ R (λ (a b : fin 3 → R),
    ![ (a 1)*(b 2) - (a 2)*(b 1) ,
       (a 2)*(b 0) - (a 0)*(b 2) ,
       (a 0)*(b 1) - (a 1)*(b 0) ]);
  intros;
  simp only [vec3_add',
    pi.add_apply, algebra.id.smul_eq_mul, matrix.smul_cons, matrix.smul_empty, pi.smul_apply];
  apply vec3_eq';
  ring,
end

localized "infixl ` ×₃ `: 68 := cross_product"      in vectors
localized "infix  ` ⬝ ` : 67 := matrix.dot_product" in vectors

lemma cross_product_def (a b : fin 3 → R) :
  a ×₃ b =
    ![ (a 1)*(b 2) - (a 2)*(b 1) ,
       (a 2)*(b 0) - (a 0)*(b 2) ,
       (a 0)*(b 1) - (a 1)*(b 0) ] :=
rfl



lemma cross_product_anticomm (v w : fin 3 → R) :
  - (v ×₃ w) = w ×₃ v :=
by simp [cross_product_def, mul_comm]

lemma cross_product_anticomm' (v w : fin 3 → R) :
  v ×₃ w + w ×₃ v = 0 :=
by rw [add_eq_zero_iff_eq_neg, cross_product_anticomm]

lemma cross_product_self_eq_zero_vector (v : fin 3 → R) :
  v ×₃ v = 0 :=
by simp [cross_product_def, mul_comm]


private lemma vec3_dot_product (v w : fin 3 → R) :
  v ⬝ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
by simp [matrix.dot_product, add_assoc, fin.sum_univ_succ]

/-- The cross product of two vectors is perpendicular to the first vector. -/
lemma dot_self_cross_product_eq_zero (v w : fin 3 → R) :
  v ⬝ (v ×₃ w) = 0 :=
by simp [cross_product_def, vec3_dot_product, mul_sub, mul_assoc, mul_left_comm]

/-- The cross product of two vectors is perpendicular to the second vector. -/
lemma dot_cross_product_self_eq_zero (v w : fin 3 → R) :
  w ⬝ (v ×₃ w) = 0 :=
by rw [← cross_product_anticomm, matrix.dot_product_neg, dot_self_cross_product_eq_zero, neg_zero]


/-- Cyclic permutations preserve the triple product. See also `triple_product_eq_det`. -/
lemma triple_product_permutation (u v w : fin 3 → R) :
  u ⬝ (v ×₃ w) = v ⬝ (w ×₃ u) :=
begin
  simp only [cross_product_def, vec3_dot_product,
    matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.empty_append, matrix.cons_val_one,
    matrix.cons_vec_alt0, matrix.cons_append, matrix.cons_val_zero],
  ring,
end

theorem triple_product_eq_det (u v w : fin 3 → R) :
  u ⬝ (v ×₃ w) = matrix.det ![ u, v, w ] :=
begin
  simp only [vec3_dot_product, cross_product_def, matrix.det_fin_three,
    matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.empty_vec_alt0, matrix.cons_vec_alt0,
    matrix.vec_head_vec_alt0, fin.fin_append_apply_zero, matrix.empty_append, matrix.cons_append,
    matrix.cons_val', matrix.cons_val_one, matrix.cons_val_zero],
  ring,
end
