/-
Copyright (c) 2022 Frédéric Dupuis, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
import algebra.group.basic

/-!
# Theory of abstract "diagonalizations"

-/

variables {E : Type*} (T : E → E)

/-- Structure encapsulating the data of a "diagonalization" -/
structure has_diagonalization
  {ι : Type*} {G : ι → Type*}
  (D : E → Π i, G i)
  (𝕜' : Type*) [Π i, has_scalar 𝕜' (G i)] :=
( eig_map : ι → 𝕜' )
( diagonalizes : ∀ i, ∀ v : E, D (T v) i = eig_map i • D v i )
