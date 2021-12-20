/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Andrew Yang
-/

import data.matrix.basic
import data.matrix.notation
import linear_algebra.basic


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
      simp [mul_add],

      have eq₀ : (a 1 * b₁ 2 + a 1 * b₂ 2) - (a 2 * b₁ 1 + a 2 * b₂ 1) =
                 (a 1 * b₁ 2 - a 2 * b₁ 1) + (a 1 * b₂ 2 - a 2 * b₂ 1),
      { ring },
      rw eq₀,

      have eq₁ : (a 2 * b₁ 0 + a 2 * b₂ 0) - (a 0 * b₁ 2 + a 0 * b₂ 2) =
                 (a 2 * b₁ 0 - a 0 * b₁ 2) + (a 2 * b₂ 0 - a 0 * b₂ 2),
      { ring },
      rw eq₁,

      have eq₂ : (a 0 * b₁ 1 + a 0 * b₂ 1) - (a 1 * b₁ 0 + a 1 * b₂ 0) =
                 (a 0 * b₁ 1 - a 1 * b₁ 0) + (a 0 * b₂ 1 - a 1 * b₂ 0),
      { ring },
      rw eq₂,

      have big : ![a 1 * b₁ 2 - a 2 * b₁ 1, a 2 * b₁ 0 - a 0 * b₁ 2, a 0 * b₁ 1 - a 1 * b₁ 0]
               + ![a 1 * b₂ 2 - a 2 * b₂ 1, a 2 * b₂ 0 - a 0 * b₂ 2, a 0 * b₂ 1 - a 1 * b₂ 0]
               = ![a 1 * b₁ 2 - a 2 * b₁ 1 + (a 1 * b₂ 2 - a 2 * b₂ 1),
                   a 2 * b₁ 0 - a 0 * b₁ 2 + (a 2 * b₂ 0 - a 0 * b₂ 2),
                   a 0 * b₁ 1 - a 1 * b₁ 0 + (a 0 * b₂ 1 - a 1 * b₂ 0)],
      { simp },

      rw ← big,
    end,

    map_smul' := λ (c : R) (b : fin 3 → R),
      by simp [mul_sub, mul_left_comm]
  },

  map_add' := λ (a₁ a₂ : fin 3 → R),
  begin
    sorry
  end,

  map_smul' := λ (c : R) (a : fin 3 → R),
  begin
    sorry
  end
}


local infix ` ×₃ `: 68 := cross_product
local infix ` ⬝ ` : 67 := matrix.dot_product



/-- cross product is anti-commutative -/
lemma cross_product_anticomm (v w : fin 3 → R) :
  v ×₃ w = - (w ×₃ v) :=
begin
  dsimp [cross_product],
  simp [mul_comm],
end

/-- vector sum of cross product with flipped cross product yields the zero vector -/
lemma cross_product_anticomm' (v w : fin 3 → R) :
  v ×₃ w + w ×₃ v = 0 :=
begin
  rw add_eq_zero_iff_eq_neg,
  apply cross_product_anticomm,
end


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
begin
  simp [cross_product, dot_product_unfold],
  simp [mul_sub, mul_assoc, mul_left_comm],
end

/-- cross product of two vectors is perpendicular to the second vector -/
lemma cross_product_perpendicular_second_arg (v w : fin 3 → R) :
  w ⬝ (v ×₃ w) = 0 :=
begin
  rw cross_product_anticomm,
  rw matrix.dot_product_neg,
  rw cross_product_perpendicular_first_arg,
  exact neg_zero,
end

/-- triple-product permutation lemma (combination of dot product with cross product);
    both terms express the determinant of [u|v|w] basically -/
lemma triple_product_permutation (u v w : fin 3 → R) :
  u ⬝ (v ×₃ w) = v ⬝ (w ×₃ u) :=
begin
  simp [cross_product, dot_product_unfold],
  simp [mul_sub, mul_assoc, mul_left_comm, mul_comm],
  ring,
end



end cross_product
