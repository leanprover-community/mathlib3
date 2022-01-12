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
@[simps] def whisker_left
  (η : oplax_nat_trans F G) {θ ι : oplax_nat_trans G H} (Γ : modification θ ι) :
    modification (η.vcomp θ) (η.vcomp ι) :=
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
@[simps] def whisker_right
  {η θ : oplax_nat_trans F G} (Γ : modification η θ) (ι : oplax_nat_trans G H) :
    modification (η.vcomp ι) (θ.vcomp ι) :=
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
@[simps] def associator
  (η : oplax_nat_trans F G) (θ : oplax_nat_trans G H) (ι : oplax_nat_trans H I) :
    (η.vcomp θ).vcomp ι ≅ η.vcomp (θ.vcomp ι) :=
modification_iso.of_components (λ a, α_ (η.app a) (θ.app a) (ι.app a))
begin
  intros a b f,
  dsimp,
  simp only [bicategory.whisker_right_comp, bicategory.whisker_left_comp, category.assoc],
  rw [←pentagon_inv_inv_hom_hom_inv_assoc, ←associator_naturality_left_assoc,
      pentagon_hom_hom_inv_hom_hom_assoc, ←associator_naturality_middle_assoc,
      ←pentagon_inv_hom_hom_hom_hom_assoc, ←associator_naturality_right_assoc,
      pentagon_hom_inv_inv_inv_hom]
end



/--
Left unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def left_unitor (η : oplax_nat_trans F G) : (oplax_nat_trans.id F).vcomp η ≅ η :=
modification_iso.of_components (λ a, λ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←left_unitor_comp, left_unitor_naturality, left_unitor_comp],
  simp
end

/--
Right unitor for the vertical composition between pseudonatural transformations.
-/
@[simps]
def right_unitor  (η : oplax_nat_trans F G) : η.vcomp (oplax_nat_trans.id G) ≅ η :=
modification_iso.of_components (λ a, ρ_ (η.app a))
begin
  intros a b f,
  dsimp,
  simp [triangle_assoc_comp_right_assoc],
  rw [←right_unitor_comp, right_unitor_naturality, right_unitor_comp],
  simp
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
{ hom := oplax_nat_trans,
  id := oplax_nat_trans.id,
  hom_category := oplax_nat_trans.category,
  comp := λ F G H, oplax_nat_trans.vcomp,
  whisker_left  := λ F G H η _ _ Γ, oplax_nat_trans.whisker_left η Γ,
  whisker_right := λ F G H _ _ Γ η, oplax_nat_trans.whisker_right Γ η,
  associator := λ F G H I, oplax_nat_trans.associator,
  left_unitor   := λ F G, oplax_nat_trans.left_unitor,
  right_unitor  := λ F G, oplax_nat_trans.right_unitor,
  associator_naturality_left'   := by { intros, ext, dsimp, rw associator_naturality_left },
  associator_naturality_middle' := by { intros, ext, dsimp, rw associator_naturality_middle },
  associator_naturality_right'  := by { intros, ext, dsimp, rw associator_naturality_right },
  left_unitor_naturality'   := by { intros, ext, dsimp, rw left_unitor_naturality },
  right_unitor_naturality'  := by { intros, ext, dsimp, rw right_unitor_naturality },
  pentagon' := by { intros, ext, dsimp, rw pentagon },
  triangle' := by { intros, ext, dsimp, rw triangle } }

end category_theory
