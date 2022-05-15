/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.alternating_face_map_complex

/-!

# Notations for the Dold-Kan equivalence

This file defines the notation `K[X] : chain_complex C ℕ` for the alternating face
map complex of `(X : simplicial_object C)` where `C` is a preadditive category, as well
as `N[X]` for the normalized subcomplex in the case `C` is an abelian category.

-/

localized "notation `K[`X`]` := algebraic_topology.alternating_face_map_complex.obj X" in dold_kan
localized "notation `N[`X`]` := algebraic_topology.normalized_Moore_complex.obj X" in dold_kan
