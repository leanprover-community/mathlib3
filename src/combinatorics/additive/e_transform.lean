/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pointwise

/-!
# Dyson's e-transform

This file
-/

open mul_opposite
open_locale pointwise

namespace finset
variables {α : Type*} [decidable_eq α] [group α] {e : α} {x : finset α × finset α}

@[to_additive]
def mul_e_transform (e : α) (x : finset α × finset α) : finset α × finset α :=
(x.1 ∩ op e • x.1, x.2 ∪ e⁻¹ • x.2)

@[simp, to_additive] lemma mul_e_transform_fst_mul_snd_subset :

end finset
