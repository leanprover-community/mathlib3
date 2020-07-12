/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import tactic.core

open tactic
/--
Demonstrate the packaged goals and how comparison of dependent goals
works.
-/
example (m n : ℕ) : m = n :=
by do
{ let tac := `[cases m; apply fin.mk.inj],
  gs₀ ← retrieve $ tac >> get_goals,
  gs₁ ← retrieve $ tac >> get_goals,
  guard (gs₀ ≠ gs₁ : bool),
  gs₀ ← get_proof_state_after tac,
  gs₁ ← get_proof_state_after tac,
  guard (gs₀ = gs₁),
  gs₀ ← get_proof_state_after $ tac >> swap,
  gs₁ ← get_proof_state_after tac,
  guard (gs₀ ≠ gs₁),
  gs₀ ← get_proof_state_after $ tac >> swap,
  gs₁ ← get_proof_state_after $ tac >> swap,
  guard (gs₀ = gs₁),
  tactic.admit }
