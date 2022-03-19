/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.natural_transformation

/-!
# The bicategory of oplax functors between two bicategories

Given bicategories `B` and `C`, we give a bicategory structure on `oplax_functor B C` whose
* objects are oplax functors,
* 1-morphisms are oplax natural transformations, and
* 2-morphisms are modifications.
-/

namespace category_theory

open category bicategory
open_locale bicategory

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
variables {F G H I : oplax_functor B C}

namespace oplax_nat_trans

/-- Left whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whisker_left (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι :=
{ app := λ a, η.app a ◁ Γ.app a,
  naturality' := λ a b f, by
  { dsimp, rw whisker_left_whisker_left_associator_inv_whisker_right_assoc, simp } }

/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whisker_right {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι :=
{ app := λ a, Γ.app a ▷ ι.app a,
  naturality' := λ a b f, by
  { dsimp,
    simp only [modification.whisker_right_naturality_assoc, iso.inv_hom_id_assoc,
      whisker_assoc_left, assoc, iso.cancel_iso_inv_left],
    rw whisker_exchange_assoc } }

/-- Associator for the vertical composition of oplax natural transformations. -/
@[simps]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ (θ ≫ ι) :=
modification_iso.of_components (λ a, α_ (η.app a) (θ.app a) (ι.app a))
begin
  intros a b f,
  dsimp,
  simp only [bicategory.whisker_left_comp, assoc, bicategory.comp_whisker_right,
    whisker_assoc_left, whisker_assoc_middle,
    pentagon_inv_hom_hom_hom_inv_assoc, whisker_assoc_right, iso.inv_hom_id_assoc,
    pentagon_inv_inv_hom_hom_inv_assoc, pentagon_inv_inv_hom_inv_inv]
end

/-- Left unitor for the vertical composition of oplax natural transformations. -/
@[simps]
def left_unitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
modification_iso.of_components (λ a, λ_ (η.app a)) (by tidy)

/-- Right unitor for the vertical composition of oplax natural transformations. -/
@[simps]
def right_unitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
modification_iso.of_components (λ a, ρ_ (η.app a)) (by tidy)

end oplax_nat_trans

variables (B C)

/-- A bicategory structure on the oplax functors between bicategories. -/
@[simps]
instance oplax_functor.bicategory : bicategory (oplax_functor B C) :=
{ whisker_left  := λ F G H η _ _ Γ, oplax_nat_trans.whisker_left η Γ,
  whisker_right := λ F G H _ _ Γ η, oplax_nat_trans.whisker_right Γ η,
  associator    := λ F G H I, oplax_nat_trans.associator,
  left_unitor   := λ F G, oplax_nat_trans.left_unitor,
  right_unitor  := λ F G, oplax_nat_trans.right_unitor,
  whisker_exchange' := by { intros, ext, apply whisker_exchange },
  associator_naturality_left'   := by { intros, ext, apply associator_naturality_left },
  associator_naturality_middle' := by { intros, ext, apply associator_naturality_middle },
  associator_naturality_right'  := by { intros, ext, apply associator_naturality_right },
  left_unitor_naturality'   := by { intros, ext, apply left_unitor_naturality },
  right_unitor_naturality'  := by { intros, ext, apply right_unitor_naturality } }

end category_theory
