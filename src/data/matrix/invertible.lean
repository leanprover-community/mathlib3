/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.invertible
import data.matrix.basic

/-! # Extra lemmas about invertible matrices

Many of the `invertible` lemmas are about `*`; this restates them to be about `⬝`.

For lemmas about the matrix inverse in terms of the determinant and adjugate, see `matrix.has_inv`
in `linear_algebra/matrix/nonsingular_inverse.lean`.
-/

open_locale matrix

variables {m n : Type*} {α : Type*}
variables [fintype n] [decidable_eq n] [semiring α]

namespace matrix

/-- A copy of `inv_of_mul_self` using `⬝` not `*`. -/
protected lemma inv_of_mul_self (A : matrix n n α) [invertible A] : ⅟A ⬝ A = 1 := inv_of_mul_self A

/-- A copy of `mul_inv_of_self` using `⬝` not `*`. -/
protected lemma mul_inv_of_self (A : matrix n n α) [invertible A] : A ⬝ ⅟A = 1 := mul_inv_of_self A

/-- A copy of `inv_of_mul_self_assoc` using `⬝` not `*`. -/
protected lemma inv_of_mul_self_assoc (A : matrix n n α) (B : matrix n m α) [invertible A] :
  ⅟A ⬝ (A ⬝ B) = B :=
by rw [←matrix.mul_assoc, matrix.inv_of_mul_self, matrix.one_mul]

/-- A copy of `mul_inv_of_self_assoc` using `⬝` not `*`. -/
protected lemma mul_inv_of_self_assoc (A : matrix n n α) (B : matrix n m α) [invertible A] :
  A ⬝ (⅟A ⬝ B) = B :=
by rw [←matrix.mul_assoc, matrix.mul_inv_of_self, matrix.one_mul]

/-- A copy of `mul_inv_of_mul_self_cancel` using `⬝` not `*`. -/
protected lemma mul_inv_of_mul_self_cancel (A : matrix m n α) (B : matrix n n α)
  [invertible B] : A ⬝ ⅟B ⬝ B = A :=
by rw [matrix.mul_assoc, matrix.inv_of_mul_self, matrix.mul_one]

/-- A copy of `mul_mul_inv_of_self_cancel` using `⬝` not `*`. -/
protected lemma mul_mul_inv_of_self_cancel (A : matrix m n α) (B : matrix n n α)
  [invertible B] : A ⬝ B ⬝ ⅟B = A :=
by rw [matrix.mul_assoc, matrix.mul_inv_of_self, matrix.mul_one]

/-- A copy of `invertible_mul` using `⬝` not `*`. -/
@[reducible] protected def invertible_mul (A B : matrix n n α) [invertible A] [invertible B] :
  invertible (A ⬝ B) :=
{ inv_of := ⅟B ⬝ ⅟A, ..invertible_mul _ _ }

/-- A copy of `invertible.mul` using `⬝` not `*`.-/
@[reducible] def _root_.invertible.matrix_mul {A B : matrix n n α}
  (ha : invertible A) (hb : invertible B) : invertible (A ⬝ B) :=
invertible_mul _ _

protected lemma inv_of_mul {A B : matrix n n α} [invertible A] [invertible B] [invertible (A ⬝ B)] :
  ⅟(A ⬝ B) = ⅟B ⬝ ⅟A := inv_of_mul _ _

/-- A copy of `invertible_of_invertible_mul` using `⬝` not `*`. -/
@[reducible] protected def invertible_of_invertible_mul (a b : matrix n n α)
  [invertible a] [invertible (a ⬝ b)] : invertible b :=
{ inv_of := ⅟(a ⬝ b) ⬝ a,
  ..invertible_of_invertible_mul a b }

/-- A copy of `invertible_of_mul_invertible` using `⬝` not `*`. -/
@[reducible] protected def invertible_of_mul_invertible (a b : matrix n n α)
  [invertible (a ⬝ b)] [invertible b] : invertible a :=
{ inv_of := b ⬝ ⅟(a ⬝ b),
  ..invertible_of_mul_invertible a b }

end matrix

/-- A copy of `invertible.mul_left` using `⬝` not `*`. -/
@[reducible] def invertible.matrix_mul_left
  {a : matrix n n α} (ha : invertible a) (b : matrix n n α) : invertible b ≃ invertible (a ⬝ b) :=
{ to_fun := λ hb, by exactI matrix.invertible_mul a b,
  inv_fun := λ hab, by exactI matrix.invertible_of_invertible_mul a _,
  left_inv := λ hb, subsingleton.elim _ _,
  right_inv := λ hab, subsingleton.elim _ _, }

/-- A copy of `invertible.mul_right` using `⬝` not `*`. -/
@[reducible] def invertible.matrix_mul_right
  (a : matrix n n α) {b : matrix n n α} (ha : invertible b) : invertible a ≃ invertible (a ⬝ b) :=
{ to_fun := λ hb, by exactI matrix.invertible_mul a b,
  inv_fun := λ hab, by exactI matrix.invertible_of_mul_invertible _ b,
  left_inv := λ hb, subsingleton.elim _ _,
  right_inv := λ hab, subsingleton.elim _ _, }
