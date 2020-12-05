/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.basic
import order.preorder_hom

/-!
# Solvable Lie algebras

This file is the place to find definitions and basic facts related to solvable Lie algebras.

## Tags

lie algebra, solvable
-/

universes u v

namespace lie_algebra

variables (R : Type u) (L : Type v)
variables [comm_ring R] [lie_ring L] [lie_algebra R L]

local notation J `/` I := (lie_ideal.comap J.incl I).quotient

/-- A Lie algebra `L` is solvable if there exists an increasing chain of ideals
`0 = I₀ ⊂ I₁ ⊂ ⋯ ⊂ Iₙ = L` such that $I_{i+1}/I_i$ is Abelian for `i = 0, 1, ..., n-1`. -/
class is_solvable : Prop :=
(solvable : ∃ (n : ℕ) (I : fin (n + 1) →ₘ lie_ideal R L),
            I 0 = ⊥ ∧ I n = ⊤ ∧ ∀ (m : fin n), is_lie_abelian (I m.succ / I m))

end lie_algebra
