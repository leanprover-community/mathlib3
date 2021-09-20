/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.vector.basic
import data.list.zip

/-!
# The `zip_with` operation on vectors.
-/

namespace vector

section zip_with

variables {α β γ : Type*} {n : ℕ} (f : α → β → γ)

/-- Apply the function `f : α → β → γ` to each corresponding pair of elements from two vectors. -/
def zip_with : vector α n → vector β n → vector γ n :=
λ x y, ⟨list.zip_with f x.1 y.1, by simp⟩

@[simp]
lemma zip_with_to_list (x : vector α n) (y : vector β n) :
  (vector.zip_with f x y).to_list = list.zip_with f x.to_list y.to_list :=
rfl

@[simp]
lemma zip_with_nth (x : vector α n) (y : vector β n) (i) :
  (vector.zip_with f x y).nth i = f (x.nth i) (y.nth i) :=
begin
  dsimp only [vector.zip_with, vector.nth],
  cases x, cases y,
  simp only [list.nth_le_zip_with, subtype.coe_mk],
  congr,
end

@[simp]
lemma zip_with_tail (x : vector α n) (y : vector β n) :
  (vector.zip_with f x y).tail = vector.zip_with f x.tail y.tail :=
by { ext, simp [nth_tail], }

end zip_with

end vector
