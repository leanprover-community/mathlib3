/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import data.sum.basic
import data.pi.algebra
/-!
# Algebraic operations and the sum type

This file provides lemmas about the interaction of the sum type with algebraic operations such as
`-`, `*`, `+`, `/`, etc.
-/

namespace sum
variables {α : Type*} {β : Type*} {γ : Type*} (x x' : α → γ) (y y' : β → γ)

lemma inv_elim [has_inv γ] :
  (sum.elim x y)⁻¹  = sum.elim x⁻¹ y⁻¹ :=
by { ext x, cases x; simp }

lemma neg_elim [has_neg γ] :
  - (sum.elim x y)  = sum.elim (- x) (- y) :=
by { ext x, cases x; simp }

lemma mul_elim [has_mul γ] :
  (sum.elim x y) * (sum.elim x' y') = sum.elim (x * x') (y * y') :=
by { ext x, cases x; simp }

lemma div_elim [has_div γ] :
  (sum.elim x y) / (sum.elim x' y') = sum.elim (x / x') (y / y') :=
by { ext x, cases x; simp }

lemma add_elim [has_add γ] :
  (sum.elim x y) + (sum.elim x' y') = sum.elim (x + x') (y + y') :=
by { ext x, cases x; simp }

lemma sub_elim [has_sub γ] :
  (sum.elim x y) - (sum.elim x' y') = sum.elim (x - x') (y - y') :=
by { ext x, cases x; simp }

end sum
