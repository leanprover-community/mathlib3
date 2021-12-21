/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser, Andrew Yang
-/

import data.matrix.basic
import data.matrix.notation
import tactic.fin_cases


namespace cross_product

variables {R : Type*} [comm_ring R]



/-- cross product of two 3D vectors -/
def cross_product : (fin 3 → R) →ₗ[R] (fin 3 → R) →ₗ[R] (fin 3 → R) :=
{
  to_fun := λ (a : fin 3 → R),

  {
    to_fun := λ (b : fin 3 → R),

      ![ (a 1)*(b 2) - (a 2)*(b 1) ,
         (a 2)*(b 0) - (a 0)*(b 2) ,
         (a 0)*(b 1) - (a 1)*(b 0) ],

    map_add' := λ (b₁ b₂ : fin 3 → R),
    begin
      ext x,
      fin_cases x; simp [mul_add]; ring,
    end,

    map_smul' := λ (c : R) (b : fin 3 → R),
      by simp [mul_sub, mul_left_comm]
  },

  map_add' := λ (a₁ a₂ : fin 3 → R),
  begin
    ext b,
    fin_cases x; simp [add_mul]; ring,
  end,

  map_smul' := λ (c : R) (a : fin 3 → R),
  begin
    ext b,
    fin_cases x; simp [mul_sub, mul_assoc],
  end
}


local infix ` ×₃ `: 68 := cross_product
local infix ` ⬝ ` : 67 := matrix.dot_product



/-- cross product is anti-commutative -/
lemma cross_product_anticomm (v w : fin 3 → R) :
  v ×₃ w = - (w ×₃ v) :=
by simp [cross_product, mul_comm]

/-- vector sum of cross product with flipped cross product yields the zero vector -/
lemma cross_product_anticomm' (v w : fin 3 → R) :
  v ×₃ w + w ×₃ v = 0 :=
by rw [add_eq_zero_iff_eq_neg, cross_product_anticomm]

/-- cross product of a vector with itself yields the zero vector -/
lemma cross_product_self_eq_zero_vector (v : fin 3 → R) :
  v ×₃ v = 0 :=
begin
  unfold cross_product,
  simp,
  split; ring_nf; tauto,
end


private lemma dot_product_unfold (v w : fin 3 → R) :
  v ⬝ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
by simp [matrix.dot_product, add_assoc, fin.sum_univ_succ]

/-- cross product of two vectors is perpendicular to the first vector -/
lemma cross_product_perpendicular_first_arg (v w : fin 3 → R) :
  v ⬝ (v ×₃ w) = 0 :=
by simp [cross_product, dot_product_unfold, mul_sub, mul_assoc, mul_left_comm]

/-- cross product of two vectors is perpendicular to the second vector -/
lemma cross_product_perpendicular_second_arg (v w : fin 3 → R) :
  w ⬝ (v ×₃ w) = 0 :=
by rw [cross_product_anticomm, matrix.dot_product_neg, cross_product_perpendicular_first_arg, neg_zero]

/-- triple-product permutation lemma (combination of dot product with cross product);
    both terms express the determinant of [u|v|w] basically -/
lemma triple_product_permutation (u v w : fin 3 → R) :
  u ⬝ (v ×₃ w) = v ⬝ (w ×₃ u) :=
begin
  simp [cross_product, dot_product_unfold, mul_sub, mul_assoc, mul_left_comm, mul_comm],
  ring,
end



end cross_product
