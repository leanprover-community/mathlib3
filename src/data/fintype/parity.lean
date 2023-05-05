/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.card
import algebra.parity

/-!
# The cardinality of `fin (bit0 n)` is even.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

namespace fintype

instance is_square.decidable_pred [has_mul α] [fintype α] [decidable_eq α] :
  decidable_pred (is_square : α → Prop) :=
λ a, fintype.decidable_exists_fintype

end fintype

/-- The cardinality of `fin (bit0 n)` is even, `fact` version.
This `fact` is needed as an instance by `matrix.special_linear_group.has_neg`. -/
lemma fintype.card_fin_even {n : ℕ} : fact (even (fintype.card (fin (bit0 n)))) :=
⟨by { rw fintype.card_fin, exact even_bit0 _ }⟩
