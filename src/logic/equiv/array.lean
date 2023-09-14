/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.vector.basic
import logic.equiv.list
import control.traversable.equiv

/-!
# Equivalences involving `array`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We keep this separate from the file containing `list`-like equivalences as those have no future
in mathlib4.
-/

namespace equiv

/-- The natural equivalence between length-`n` heterogeneous arrays
and dependent functions from `fin n`. -/
def d_array_equiv_fin {n : ℕ} (α : fin n → Type*) : d_array n α ≃ (Π i, α i) :=
⟨d_array.read, d_array.mk, λ ⟨f⟩, rfl, λ f, rfl⟩

/-- The natural equivalence between length-`n` arrays and functions from `fin n`. -/
def array_equiv_fin (n : ℕ) (α : Type*) : array n α ≃ (fin n → α) :=
d_array_equiv_fin _

/-- The natural equivalence between length-`n` vectors and length-`n` arrays. -/
def vector_equiv_array (α : Type*) (n : ℕ) : vector α n ≃ array n α :=
(vector_equiv_fin _ _).trans (array_equiv_fin _ _).symm

end equiv

namespace array
open function
variable {n : ℕ}

instance : traversable (array n) :=
@equiv.traversable (flip vector n) _ (λ α, equiv.vector_equiv_array α n) _

instance : is_lawful_traversable (array n) :=
@equiv.is_lawful_traversable (flip vector n) _ (λ α, equiv.vector_equiv_array α n) _ _

end array

/-- If `α` is encodable, then so is `array n α`. -/
instance _root_.array.encodable {α} [encodable α] {n} : encodable (array n α) :=
encodable.of_equiv _ (equiv.array_equiv_fin _ _)

/-- If `α` is countable, then so is `array n α`. -/
instance _root_.array.countable {α} [countable α] {n} : countable (array n α) :=
countable.of_equiv _ (equiv.vector_equiv_array _ _)
