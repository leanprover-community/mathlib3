/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.p_infty

/-!

# Construction of functors N for the Dold-Kan correspondence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

TODO (@joelriou) continue adding the various files referenced below

In this file, we construct functors `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`
and `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
for any preadditive category `C`. (The indices of these functors are the number of occurrences
of `karoubi` at the source or the target.)

In the case `C` is additive, the functor `N₂` shall be the functor of the equivalence
`category_theory.preadditive.dold_kan.equivalence` defined in `equivalence_additive.lean`.

In the case the category `C` is pseudoabelian, the composition of `N₁` with the inverse of the
equivalence `chain_complex C ℕ ⥤ karoubi (chain_complex C ℕ)` will be the functor
`category_theory.idempotents.dold_kan.N` of the equivalence of categories
`category_theory.idempotents.dold_kan.equivalence : simplicial_object C ≌ chain_complex C ℕ`
defined in `equivalence_pseudoabelian.lean`.

When the category `C` is abelian, a relation between `N₁` and the
normalized Moore complex functor shall be obtained in `normalized.lean`.

(See `equivalence.lean` for the general strategy of proof.)

-/

open category_theory
open category_theory.category
open category_theory.idempotents

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

/-- The functor `simplicial_object C ⥤ karoubi (chain_complex C ℕ)` which maps
`X` to the formal direct factor of `K[X]` defined by `P_infty`. -/
@[simps]
def N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ) :=
{ obj := λ X,
  { X := alternating_face_map_complex.obj X,
    p := P_infty,
    idem := P_infty_idem, },
  map := λ X Y f,
  { f := P_infty ≫ alternating_face_map_complex.map f,
    comm := by { ext, simp }, },
  map_id' := λ X, by { ext, dsimp, simp },
  map_comp' := λ X Y Z f g, by { ext, simp } }

/-- The extension of `N₁` to the Karoubi envelope of `simplicial_object C`. -/
@[simps]
def N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) :=
(functor_extension₁ _ _).obj N₁

end dold_kan

end algebraic_topology
