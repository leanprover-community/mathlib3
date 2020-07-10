/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.adjunction.basic
import category_theory.yoneda

open category_theory

namespace category_theory
universes v₁ v₂ u₁ u₂

open category
open opposite

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

-- Lemma 4.5.13 from [Riehl][riehl2017]
-- Proof in <https://stacks.math.columbia.edu/tag/0036>
-- or at <https://math.stackexchange.com/a/2727177>
instance unit_is_iso_of_L_fully_faithful [full L] [faithful L] : is_iso (adjunction.unit h) :=
@nat_iso.is_iso_of_is_iso_app _ _ _ _ _ _ (adjunction.unit h) $ λ X,
@yoneda.is_iso _ _ _ _ ((adjunction.unit h).app X)
{ inv := { app := λ Y f, L.preimage ((h.hom_equiv (unop Y) (L.obj X)).symm f) },
  inv_hom_id' :=
  begin
    ext, dsimp,
    simp only [adjunction.hom_equiv_counit, preimage_comp, preimage_map, category.assoc],
    rw ←h.unit_naturality,
    simp,
  end,
  hom_inv_id' :=
  begin
    ext, dsimp,
    apply L.map_injective,
    simp,
  end }.

instance counit_is_iso_of_R_fully_faithful [full R] [faithful R] : is_iso (adjunction.counit h) :=
@nat_iso.is_iso_of_is_iso_app _ _ _ _ _ _ (adjunction.counit h) $ λ X,
@is_iso_of_op _ _ _ _ _ $
@coyoneda.is_iso _ _ _ _ ((adjunction.counit h).app X).op
{ inv := { app := λ Y f, R.preimage ((h.hom_equiv (R.obj X) Y) f) },
  inv_hom_id' :=
  begin
    ext, dsimp,
    simp only [adjunction.hom_equiv_unit, preimage_comp, preimage_map],
    rw ←h.counit_naturality,
    simp,
  end,
  hom_inv_id' :=
  begin
    ext, dsimp,
    apply R.map_injective,
    simp,
  end }

-- TODO also prove the converses?
-- def L_full_of_unit_is_iso [is_iso (adjunction.unit h)] : full L := sorry
-- def L_faithful_of_unit_is_iso [is_iso (adjunction.unit h)] : faithful L := sorry
-- def R_full_of_counit_is_iso [is_iso (adjunction.counit h)] : full R := sorry
-- def R_faithful_of_counit_is_iso [is_iso (adjunction.counit h)] : faithful R := sorry

-- TODO also do the statements from Riehl 4.5.13 for full and faithful separately?


end category_theory
