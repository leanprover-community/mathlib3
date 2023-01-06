/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.repr
import data.finset.sort

/-!
# Representing a finset as a string
-/

instance {α : Type*} [has_repr α] : has_repr (finset α) := ⟨λ s, repr s.1⟩
