/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández

Localization of topological rings.
-/
import topology.algebra.ring
import ring_theory.localization

/-!

# Localization of topological rings

The topological localization of a topological commutative ring `R` at a submonoid `M` is the ring
`localization M`  endowed with the final ring topology of the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)` in the localization of `R` at a `M`.

## Main Results

- `localization.topological_ring`: The localization of a topological commutative ring at a submonoid
  is a topological ring.

-/

instance {α : Type*}
  [comm_ring α][t: topological_space α]{x: submonoid α} : ring_topology (localization x) :=
ring_topology.coinduced (localization.monoid_of x).to_fun t

instance {α : Type*}
  [comm_ring α][topological_space α]{x: submonoid α} : topological_ring (localization x) :=
localization.ring_topology.to_topological_ring
