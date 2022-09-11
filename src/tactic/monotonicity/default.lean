/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.monotonicity.interactive
import tactic.monotonicity.lemmas

example {α : Type*} [linear_ordered_ring α]
  (x y z a : α) (h₁ : 0 ≤ a) (h₂ : y ≤ z) :
  (x * y) * a ≤ (x * z) * a :=
begin
  mono*,
  apply_instance, apply_instance,
end
