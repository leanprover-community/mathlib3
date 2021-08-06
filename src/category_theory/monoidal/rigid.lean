/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/

import category_theory.monoidal.category

open category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]

/- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
class exact_pairing (X Y : C) :=
  (coevaluation [] : 𝟙_ C ⟶ X ⊗ Y)
  (evaluation [] : Y ⊗ X ⟶ 𝟙_ C)
  (coevaluation_evaluation' [] :
    (𝟙 Y ⊗ coevaluation) ≫ (α_ _ _ _).inv ≫ (evaluation ⊗ 𝟙 Y)
    = (ρ_ Y).hom ≫ (λ_ Y).inv . obviously)
  (evaluation_coevaluation' [] :
    (coevaluation ⊗ 𝟙 X) ≫ (α_ _ _ _).hom ≫ (𝟙 X ⊗ evaluation)
    = (λ_ X).hom ≫ (ρ_ X).inv . obviously)

open exact_pairing

notation `η_` := exact_pairing.coevaluation
notation `ε_` := exact_pairing.evaluation

restate_axiom coevaluation_evaluation'
attribute [reassoc, simp] exact_pairing.coevaluation_evaluation
restate_axiom evaluation_coevaluation'
attribute [reassoc, simp] exact_pairing.evaluation_coevaluation

instance exact_pairing_unit : exact_pairing (𝟙_ C) (𝟙_ C) :=
{ coevaluation := (ρ_ _).inv,
  evaluation := (ρ_ _).hom,
  coevaluation_evaluation' := by {
    rw[monoidal_category.triangle_assoc_comp_right,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp },
  evaluation_coevaluation' := by {
    rw[monoidal_category.triangle_assoc_comp_right_inv_assoc,
      monoidal_category.unitors_inv_equal,
      monoidal_category.unitors_equal], simp } }

/- A class of objects which have a right dual, -/
class has_right_dual (X : C) :=
  (right_dual : C)
  [exact : exact_pairing X right_dual]

/- ... and a class of objects with have a left dual.-/
class has_left_dual (Y : C) :=
  (left_dual : C)
  [exact : exact_pairing left_dual Y]

attribute [instance] has_right_dual.exact
attribute [instance] has_left_dual.exact

open exact_pairing has_right_dual has_left_dual monoidal_category

reserve prefix `*^`:1025
notation `*^` X := left_dual X
reserve postfix `^*`:1025
notation X `^*` := right_dual X

instance has_right_dual_unit : has_right_dual (𝟙_ C) :=
{ right_dual := 𝟙_ C }

instance has_left_dual_unit : has_left_dual (𝟙_ C) :=
{ left_dual := 𝟙_ C }

instance has_right_dual_left_dual {X : C} [has_left_dual X] : has_right_dual (*^X) :=
{ right_dual := X }

instance has_left_dual_right_dual {X : C} [has_right_dual X] : has_left_dual (X ^*) :=
{ left_dual := X }

theorem left_dual_right_dual {X : C} [has_right_dual X] : *^(X^*) = X := rfl

theorem right_dual_left_dual {X : C} [has_left_dual X] : (*^X)^* = X := rfl

def right_adjoint_mate {X Y : C} [has_right_dual X] [has_right_dual Y] (f : X ⟶ Y) : Y^* ⟶ X^* :=
(ρ_ _).inv ≫ (𝟙 _ ⊗ η_ _ _) ≫ (𝟙 _ ⊗ (f ⊗ 𝟙 _)) ≫ (α_ _ _ _).inv ≫ ((ε_ _ _) ⊗ 𝟙 _) ≫ (λ_ _).hom

notation f `^*` := right_adjoint_mate f

@[simp] --Do we want this to be simp?
theorem right_adjoint_mate_id {X : C} [has_right_dual X] : (𝟙 X)^* = 𝟙 (X^*) :=
begin
  simp only [right_adjoint_mate, monoidal_category.tensor_id, category.id_comp],
  slice_lhs 2 4 { rw coevaluation_evaluation },
  simp
end

theorem right_adjoint_mate_comp {X Y Z : C} [has_right_dual X]
  [has_right_dual Y] {f : X ⟶ Y} {g : X^* ⟶ Z} :
  f^* ≫ g
  = (ρ_ Y^*).inv ≫ (𝟙 _ ⊗ η_ X X^*) ≫ (𝟙 _ ⊗ f ⊗ g)
    ≫ (α_ Y^* Y Z).inv ≫ (ε_ Y Y^* ⊗ 𝟙 _) ≫ (λ_ Z).hom :=
begin
  dunfold right_adjoint_mate,
  slice_lhs 3 4 { rw associator_inv_naturality },
  slice_rhs 3 4 { rw associator_inv_naturality },
  rw ←tensor_id_comp_id_tensor g,
  slice_rhs 5 6 { rw id_tensor_comp_tensor_id },
  slice_lhs 6 7 { rw ←left_unitor_naturality },
  rw tensor_id_comp_id_tensor_assoc
end

/- The composition of adjoint mates is the adjoint mate of the composition. -/
theorem comp_right_adjoint_mate {X Y Z : C}
  [has_right_dual X] [has_right_dual Y] [has_right_dual Z] {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g)^* = g^* ≫ f^* :=
begin
  rw right_adjoint_mate_comp,
  simp only [right_adjoint_mate, comp_tensor_id, iso.cancel_iso_inv_left, id_tensor_comp, category.assoc],
  symmetry, iterate 5 { transitivity, rw [←category.id_comp g, tensor_comp] },
  rw [←category.assoc],
  symmetry, iterate 2 { transitivity, rw ←category.assoc }, apply eq_whisker,
  repeat { rw ←id_tensor_comp }, apply congr_arg (λ f, 𝟙 Z^* ⊗ f),
  slice_rhs 7 8 { rw ←id_tensor_comp_tensor_id },
  rw id_tensor_right_unitor_inv,
  slice_rhs 1 2 { rw right_unitor_inv_naturality },
  slice_rhs 3 4 { rw ←associator_naturality },
  slice_rhs 2 3 { rw [tensor_id, tensor_id_comp_id_tensor] },
  slice_rhs 3 4 { rw ←associator_naturality },
  slice_rhs 2 3 { rw [←tensor_comp, tensor_id, category.comp_id, ←category.id_comp (η_ Y Y^*), tensor_comp] },
  slice_rhs 3 3 { rw ←id_tensor_comp_tensor_id }, rw ←tensor_id,
  slice_rhs 5 6 { rw pentagon_hom_inv },
  slice_rhs 7 8 { rw ←associator_naturality },
  slice_rhs 4 5 { rw associator_inv_naturality },
  slice_rhs 5 7 { rw [←comp_tensor_id, ←comp_tensor_id, evaluation_coevaluation, comp_tensor_id] },
  slice_rhs 3 4 { rw associator_inv_naturality },
  slice_rhs 4 5 { rw [←tensor_comp, left_unitor_naturality, tensor_comp] },
  slice_rhs 5 7 { rw [triangle_assoc_comp_right_inv, tensor_id_comp_id_tensor] },
  slice_rhs 5 6 { rw [tensor_inv_hom_id, category.comp_id] },
  slice_rhs 3 4 { rw ←left_unitor_tensor },
  slice_rhs 2 3 { rw left_unitor_naturality },
  rw [unitors_equal, ←category.assoc, ←category.assoc], simp
end

/- This theorem shows that right duals are isomorphic, which is almost trivial due to the
  previous theorem. -/
theorem right_dual_iso {X Y₁ Y₂ : C} (p₁ : exact_pairing X Y₁) (p₂ : exact_pairing X Y₂) :
  Y₁ ≅ Y₂ :=
{ hom := @right_adjoint_mate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X),
  inv := @right_adjoint_mate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X),
  hom_inv_id' := by rw [←comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id],
  inv_hom_id' := by rw [←comp_right_adjoint_mate, category.comp_id, right_adjoint_mate_id] }

/- A right rigid monoidal category is one in which every object has a right dual. -/
class right_rigid_category (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
  (dual : Π (X : C), has_right_dual X)

attribute [instance] right_rigid_category.dual

end category_theory
