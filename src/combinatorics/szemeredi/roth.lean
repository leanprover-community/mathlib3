/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .triangle

/-!
# Roth's theorem

This file proves Roth's theorem
-/

open finset

lemma roth (N : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ n, N ≤ n → ∀ A ⊆ range n, δ * n ≤ A.card → ∃ a d,
  a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
sorry
