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

/-- The graph used in the proof of Roth's theorem. -/
def roth_graph (n : ℕ) : simple_graph (fin 3 × fin (2 * n + 1)) :=
simple_graph.from_rel (λ a b, begin
    refine if a = 0 then
  end)

lemma roth_triangle_free_far (n : ℕ) (ε : ℝ) : (roth_graph n).triangle_free_far ε :=
begin
  sorry
end

lemma roth (N : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ n, N ≤ n → ∀ A ⊆ range n, δ * n ≤ A.card → ∃ a d,
  a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
begin
end
