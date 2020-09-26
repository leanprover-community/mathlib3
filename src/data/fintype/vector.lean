/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.fintype.basic
import data.array.lemmas

/-! # Fintype instances for arrays and vectors


## Implementation details

We put these instances in a separate file from `data.fintype.basic` to keep them out of the
import graph of `tactic.linarith`.

-/

instance d_array.fintype {n : ℕ} {α : fin n → Type*}
  [∀n, fintype (α n)] : fintype (d_array n α) :=
fintype.of_equiv _ (equiv.d_array_equiv_fin _).symm

instance array.fintype {n : ℕ} {α : Type*} [fintype α] : fintype (array n α) :=
d_array.fintype

instance vector.fintype {α : Type*} [fintype α] {n : ℕ} : fintype (vector α n) :=
fintype.of_equiv _ (equiv.vector_equiv_fin _ _).symm
