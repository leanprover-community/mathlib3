 /-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.natural_transformation


namespace category_theory

open category bicategory
open_locale bicategory

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
variables {F G H I : oplax_functor B C}

namespace oplax_nat_trans

/--
Left whiskering of a pseudonatural transformation and a modification.
-/
@[simps]
def whisker_left (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι :=
{ app := λ a, η.app a ◁ Γ.app a,
  naturality' := λ a b f, by
  { dsimp,
    simp only [assoc],
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
        associator_naturality_right_assoc, Γ.whisker_left_naturality_assoc,
        associator_inv_naturality_middle] } }

/--
Right whiskering of a pseudonatural transformation and a modification.
-/
@[simps]
def whisker_right {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι :=
{ app := λ a, Γ.app a ▷ ι.app a,
  naturality' := λ a b f, by
  { dsimp,
    simp only [assoc],
    rw [associator_inv_naturality_middle_assoc, Γ.whisker_right_naturality_assoc,
        associator_naturality_left_assoc, ←whisker_exchange_assoc,
        associator_inv_naturality_left] } }

/--
Associator for the vertical composition between pseudonatural transformations.
-/
@[simps]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ (θ ≫ ι) :=
modification_iso.of_components (λ a, α_ (η.app a) (θ.app a) (ι.app a))
begin
  intros a b f,
  dsimp,
  simp only [whisker_right_comp, whisker_left_comp, assoc],
  rw [←pentagon_inv_inv_hom_hom_inv_assoc, ←associator_naturality_left_assoc,
      pentagon_hom_hom_inv_hom_hom_assoc, ←associator_naturality_middle_assoc,
      ←pentagon_inv_hom_hom_hom_hom_assoc, ←associator_naturality_right_assoc,
      pentagon_hom_inv_inv_inv_hom]
end



/--
Left unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def left_unitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
modification_iso.of_components (λ a, λ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←left_unitor_comp, left_unitor_naturality, left_unitor_comp],
  simp only [iso.hom_inv_id_assoc, inv_hom_whisker_right_assoc, assoc, whisker_exchange_assoc]
end

/--
Right unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def right_unitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
modification_iso.of_components (λ a, ρ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←right_unitor_comp, right_unitor_naturality, right_unitor_comp],
  simp only [iso.inv_hom_id_assoc, assoc]
end

end oplax_nat_trans

variables (B C)

/--
A bicategory structure on the oplax_functors between bicategories. The 1-morphisms in this bicategory are
the pseudonatural transformations, and the composition of 1-morphisms is the vertical composition
of pseudonatural transformations. The 2-morphisms are the modifications.
-/
@[simps]
instance oplax_functor.bicategory : bicategory (oplax_functor B C) :=
{ whisker_left  := λ F G H η _ _ Γ, oplax_nat_trans.whisker_left η Γ,
  whisker_right := λ F G H _ _ Γ η, oplax_nat_trans.whisker_right Γ η,
  associator := λ F G H I, oplax_nat_trans.associator,
  left_unitor   := λ F G, oplax_nat_trans.left_unitor,
  right_unitor  := λ F G, oplax_nat_trans.right_unitor,
  associator_naturality_left'   := by { intros, ext, apply associator_naturality_left },
  associator_naturality_middle' := by { intros, ext, apply associator_naturality_middle },
  associator_naturality_right'  := by { intros, ext, apply associator_naturality_right },
  left_unitor_naturality'   := by { intros, ext, apply left_unitor_naturality },
  right_unitor_naturality'  := by { intros, ext, apply right_unitor_naturality },
  pentagon' := by { intros, ext, apply pentagon },
  triangle' := by { intros, ext, apply triangle } }

end category_theory
