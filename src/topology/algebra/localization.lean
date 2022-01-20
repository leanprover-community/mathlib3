/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.localization
import topology.algebra.ring

/-!

# Localization of topological rings

The topological localization of a topological commutative ring `R` at a submonoid `M` is the ring
`localization M`  endowed with the final ring topology of the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)` in the localization of `R` at a `M`.

## Main Results

- `localization.topological_ring`: The localization of a topological commutative ring at a submonoid
  is a topological ring.

-/

variables {R : Type*} [comm_ring R] [topological_space R] {M : submonoid R}

/-- The ring topology on `localization M` coinduced from the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)`. -/
def localization.ring_topology : ring_topology (localization M) :=
ring_topology.coinduced (localization.monoid_of M).to_fun

instance : topological_space (localization M) :=
localization.ring_topology.to_topological_space

instance : topological_ring (localization M) :=
localization.ring_topology.to_topological_ring
