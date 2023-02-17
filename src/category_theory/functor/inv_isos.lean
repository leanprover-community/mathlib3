/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/

import category_theory.eq_to_hom

/-!
# Natural isomorphisms with composition with inverses

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Definition of useful natural isomorphisms involving inverses of functors.
These definitions cannot go in `category_theory/equivalence` because they require `eq_to_hom`.
-/

namespace category_theory

open category_theory.functor

universes u₁ u₂ u₃ v₁ v₂ v₃

variables {A : Type u₁} [category.{v₁} A]
          {B : Type u₂} [category.{v₂} B]
          {C : Type u₃} [category.{v₃} C]

variables {F : A ⥤ C} {G : A ⥤ B} {H : B ⥤ C}

/-- Construct an isomorphism `F ⋙ H.inv ≅ G` from an isomorphism `F ≅ G ⋙ H`. -/
@[simps] def comp_inv_iso [h : is_equivalence H] (i : F ≅ G ⋙ H) : F ⋙ H.inv ≅ G :=
iso_whisker_right i H.inv ≪≫ (associator G H H.inv) ≪≫
iso_whisker_left G h.unit_iso.symm ≪≫ eq_to_iso (functor.comp_id G)

/-- Construct an isomorphism `G ≅ F ⋙ H.inv` from an isomorphism `G ⋙ H ≅ F`. -/
@[simps] def iso_comp_inv [h : is_equivalence H] (i : G ⋙ H ≅ F) : G ≅ F ⋙ H.inv :=
(comp_inv_iso i.symm).symm

/-- Construct an isomorphism `G.inv ⋙ F ≅ H` from an isomorphism `F ≅ G ⋙ H`. -/
@[simps] def inv_comp_iso [h : is_equivalence G] (i : F ≅ G ⋙ H) : G.inv ⋙ F ≅ H :=
iso_whisker_left G.inv i ≪≫ (associator G.inv G H).symm ≪≫
iso_whisker_right h.counit_iso H ≪≫ eq_to_iso (functor.id_comp H)

/-- Construct an isomorphism `H ≅ G.inv ⋙ F` from an isomorphism `G ⋙ H ≅ F`. -/
@[simps] def iso_inv_comp [h : is_equivalence G] (i : G ⋙ H ≅ F) : H ≅ G.inv ⋙ F :=
(inv_comp_iso i.symm).symm

end category_theory
