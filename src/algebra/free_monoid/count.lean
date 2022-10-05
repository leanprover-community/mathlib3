/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.free_monoid.basic
import data.list.count

/-!
-/

variables {α : Type*} (p : α → Prop) [decidable_pred p]

namespace free_add_monoid

def countp (p : α → Prop) [decidable_pred p] : free_add_monoid α →+ ℕ :=
⟨list.countp p, list.countp_nil p, list.countp_append _⟩

lemma countp_of (x : α) : countp p (of x) = if p x then 1 else 0 := rfl

def count [decidable_eq α] (x : α) : free_add_monoid α →+ ℕ := countp (eq x)

lemma count_of [decidable_eq α] (x y : α) : count x (of y) = pi.single x 1 y :=
by simp only [count, countp_of, pi.single_apply, eq_comm]

end free_add_monoid

namespace free_monoid

end free_monoid
