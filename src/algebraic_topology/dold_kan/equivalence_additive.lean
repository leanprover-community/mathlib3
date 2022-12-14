/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.n_comp_gamma

/-! The Dold-Kan equivalence for additive categories.

This file defines `preadditive.dold_kan.equivalence` which is the equivalence
of categories `karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)`.

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.idempotents algebraic_topology.dold_kan

variables {C : Type*} [category C] [preadditive C]

namespace category_theory

namespace preadditive

namespace dold_kan

/-- The functor `karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)` of
the Dold-Kan equivalence for additive categories. -/
@[simps]
def N : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) := N₂

variable [has_finite_coproducts C]

/-- The inverse functor `karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` of
the Dold-Kan equivalence for additive categories. -/
@[simps]
def Γ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) := Γ₂

/-- The Dold-Kan equivalence `karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)`
for additive categories. -/
@[simps]
def equivalence : karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ) :=
{ functor := N,
  inverse := Γ,
  unit_iso := Γ₂N₂,
  counit_iso := N₂Γ₂,
  functor_unit_iso_comp' := λ P, begin
    let α := N.map_iso (Γ₂N₂.app P),
    let β := N₂Γ₂.app (N.obj P),
    symmetry,
    change 𝟙 _ = α.hom ≫ β.hom,
    rw [← iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← iso.inv_comp_eq],
    exact algebraic_topology.dold_kan.identity_N₂_objectwise P,
  end }

end dold_kan

end preadditive

end category_theory
