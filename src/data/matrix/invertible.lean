/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.invertible
import data.matrix.basic

/-! # Extra lemmas about invertible matrices

Many of the `invertible` lemmas are about `*`; this restates them to be about `⬝`.
-/

variables {m n : Type*} {α : Type*}
variables [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]

-- TODO: move these lemmas to `algebra/invertible` after the port
section to_move
variables {M : Type*} [monoid M]

/-- If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s = si`. -/
@[reducible] def invertible.copy' {α} [mul_one_class α] {r : α} (hr : invertible r) (s : α) (si : α)
  (hs : s = r) (hsi : si = ⅟r) :
  invertible s :=
{ inv_of := si,
  inv_of_mul_self := by rw [hs, hsi, inv_of_mul_self],
  mul_inv_of_self := by rw [hs, hsi, mul_inv_of_self] }

/-- A copy of `invertible_mul` for dot notation. -/
@[reducible] def invertible.mul {a b : M} (ha : invertible a) (hb : invertible b) :
  invertible (a * b) :=
invertible_mul _ _

/-- This is the `invertible` version of `units.is_unit_units_mul` -/
@[reducible] def invertible_of_invertible_mul (a b : M) [invertible a] [invertible (a * b)] :
  invertible b :=
{ inv_of := ⅟(a * b) * a,
  inv_of_mul_self := by rw [mul_assoc, inv_of_mul_self],
  mul_inv_of_self := by rw [←(is_unit_of_invertible a).mul_right_inj, ←mul_assoc, ←mul_assoc,
    mul_inv_of_self, mul_one, one_mul] }

/-- This is the `invertible` version of `units.is_unit_mul_units` -/
@[reducible] def invertible_of_mul_invertible (a b : M) [invertible (a * b)] [invertible b] :
  invertible a :=
{ inv_of := b * ⅟(a * b),
  inv_of_mul_self := by rw [←(is_unit_of_invertible b).mul_left_inj, mul_assoc, mul_assoc,
    inv_of_mul_self, mul_one, one_mul],
  mul_inv_of_self := by rw [←mul_assoc, mul_inv_of_self] }

/-- `invertible_of_invertible_mul` and `invertible_mul` as an equivalence. -/
@[simps] def invertible.mul_left {a : M} (ha : invertible a) (b : M) :
  invertible b ≃ invertible (a * b) :=
{ to_fun := λ hb, by exactI invertible_mul a b,
  inv_fun := λ hab, by exactI invertible_of_invertible_mul a _,
  left_inv := λ hb, subsingleton.elim _ _,
  right_inv := λ hab, subsingleton.elim _ _, }

/-- `invertible_of_mul_invertible` and `invertible_mul` as an equivalence. -/
@[simps] def invertible.mul_right (a : M) {b : M} (ha : invertible b) :
  invertible a ≃ invertible (a * b) :=
{ to_fun := λ hb, by exactI invertible_mul a b,
  inv_fun := λ hab, by exactI invertible_of_mul_invertible _ b,
  left_inv := λ hb, subsingleton.elim _ _,
  right_inv := λ hab, subsingleton.elim _ _, }

end to_move

open_locale matrix

variables [semiring α]

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
{ to_fun := λ hb, by exactI invertible_mul a b,
  inv_fun := λ hab, by exactI invertible_of_invertible_mul a _,
  left_inv := λ hb, subsingleton.elim _ _,
  right_inv := λ hab, subsingleton.elim _ _, }

/-- A copy of `invertible.mul_right` using `⬝` not `*`. -/
@[reducible] def invertible.matrix_mul_right
  (a : matrix n n α) {b : matrix n n α} (ha : invertible b) : invertible a ≃ invertible (a ⬝ b) :=
{ to_fun := λ hb, by exactI invertible_mul a b,
  inv_fun := λ hab, by exactI invertible_of_mul_invertible _ b,
  left_inv := λ hb, subsingleton.elim _ _,
  right_inv := λ hab, subsingleton.elim _ _, }
