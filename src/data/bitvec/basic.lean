
/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.bitvec
import order.basic

instance (n : ℕ) : preorder (bitvec n) :=
preorder.lift bitvec.to_nat

lemma bitvec.le_def {n : ℕ} (x y : bitvec n) :
  x ≤ y ↔ x.to_nat ≤ y.to_nat :=
iff.rfl
