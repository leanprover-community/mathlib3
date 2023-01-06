/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.sort
import data.string.basic

/-!
# Representing a multiset as a string
-/

instance {α : Type*} [has_repr α] : has_repr (multiset α) :=
⟨λ s, "{" ++ string.intercalate ", " ((s.map repr).sort (≤)) ++ "}"⟩
