/-
  Copyright (c) 2020 Anne Baanen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Anne Baanen
-/
import tactic.simp_rw
import data.set.basic

-- `simp_rw` can perform rewrites under binders:
example : (λ (x y : ℕ), x + y) = (λ x y, y + x) := by simp_rw [add_comm]

-- `simp_rw` performs rewrites in the given order (`simp` fails on this example):
example {α β : Type} {f : α → β} {t : set β} :
  (∀ s, f '' s ⊆ t) = ∀ s : set α, ∀ x ∈ s, x ∈ f ⁻¹' t :=
by simp_rw [set.image_subset_iff, set.subset_def]

-- `simp_rw` applies rewrite rules multiple times:
example (a b c d : ℕ) : a + (b + (c + d)) = ((d + c) + b) + a := by simp_rw [add_comm]

-- `simp_rw` can also rewrite in assumptions:
example (p : ℕ → Prop) (a b : ℕ) (h : p (a + b)) : p (b + a) :=
by {simp_rw [add_comm a b] at h, exact h}
