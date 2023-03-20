/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.additive_functor
import category_theory.monoidal.functor

/-!
# Preadditive monoidal categories

A monoidal category is `monoidal_preadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/

noncomputable theory
open_locale classical

namespace category_theory

open category_theory.limits
open category_theory.monoidal_category

variables (C : Type*) [category C] [preadditive C] [monoidal_category C]

/--
A category is `monoidal_preadditive` if tensoring is additive in both factors.

Note we don't `extend preadditive C` here, as `abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class monoidal_preadditive : Prop :=
(tensor_zero' : ∀ {W X Y Z : C} (f : W ⟶ X), f ⊗ (0 : Y ⟶ Z) = 0 . obviously)
(zero_tensor' : ∀ {W X Y Z : C} (f : Y ⟶ Z), (0 : W ⟶ X) ⊗ f = 0 . obviously)
(tensor_add' : ∀ {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z), f ⊗ (g + h) = f ⊗ g + f ⊗ h . obviously)
(add_tensor' : ∀ {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z), (f + g) ⊗ h = f ⊗ h + g ⊗ h . obviously)

restate_axiom monoidal_preadditive.tensor_zero'
restate_axiom monoidal_preadditive.zero_tensor'
restate_axiom monoidal_preadditive.tensor_add'
restate_axiom monoidal_preadditive.add_tensor'
attribute [simp] monoidal_preadditive.tensor_zero monoidal_preadditive.zero_tensor

variables {C} [monoidal_preadditive C]

local attribute [simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance tensor_left_additive (X : C) : (tensor_left X).additive := {}
instance tensor_right_additive (X : C) : (tensor_right X).additive := {}
instance tensoring_left_additive (X : C) : ((tensoring_left C).obj X).additive := {}
instance tensoring_right_additive (X : C) : ((tensoring_right C).obj X).additive := {}

/-- A faithful additive monoidal functor to a monoidal preadditive category
ensures that the domain is monoidal preadditive. -/
lemma monoidal_preadditive_of_faithful {D} [category D] [preadditive D] [monoidal_category D]
  (F : monoidal_functor D C) [faithful F.to_functor] [F.to_functor.additive] :
  monoidal_preadditive D :=
{ tensor_zero' := by { intros, apply F.to_functor.map_injective, simp [F.map_tensor], },
  zero_tensor' := by { intros, apply F.to_functor.map_injective, simp [F.map_tensor], },
  tensor_add' := begin
    intros,
    apply F.to_functor.map_injective,
    simp only [F.map_tensor, F.to_functor.map_add, preadditive.comp_add, preadditive.add_comp,
      monoidal_preadditive.tensor_add],
  end,
  add_tensor' := begin
    intros,
    apply F.to_functor.map_injective,
    simp only [F.map_tensor, F.to_functor.map_add, preadditive.comp_add, preadditive.add_comp,
      monoidal_preadditive.add_tensor],
  end, }

open_locale big_operators

lemma tensor_sum {P Q R S : C} {J : Type*} (s : finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
  f ⊗ ∑ j in s, g j = ∑ j in s, f ⊗ g j :=
begin
  rw ←tensor_id_comp_id_tensor,
  let tQ := (((tensoring_left C).obj Q).map_add_hom : (R ⟶ S) →+ _),
  change _ ≫ tQ _ = _,
  rw [tQ.map_sum, preadditive.comp_sum],
  dsimp [tQ],
  simp only [tensor_id_comp_id_tensor],
end

lemma sum_tensor {P Q R S : C} {J : Type*} (s : finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
  (∑ j in s, g j) ⊗ f = ∑ j in s, g j ⊗ f :=
begin
  rw ←tensor_id_comp_id_tensor,
  let tQ := (((tensoring_right C).obj P).map_add_hom : (R ⟶ S) →+ _),
  change tQ _ ≫ _ = _,
  rw [tQ.map_sum, preadditive.sum_comp],
  dsimp [tQ],
  simp only [tensor_id_comp_id_tensor],
end

variables {C}

-- In a closed monoidal category, this would hold because
-- `tensor_left X` is a left adjoint and hence preserves all colimits.
-- In any case it is true in any preadditive category.
instance (X : C) : preserves_finite_biproducts (tensor_left X) :=
{ preserves := λ J _, by exactI
  { preserves := λ f,
    { preserves := λ b i, is_bilimit_of_total _ begin
      dsimp,
      simp only [←tensor_comp, category.comp_id, ←tensor_sum, ←tensor_id, is_bilimit.total i],
    end } } }

instance (X : C) : preserves_finite_biproducts (tensor_right X) :=
{ preserves := λ J _, by exactI
  { preserves := λ f,
    { preserves := λ b i, is_bilimit_of_total _ begin
      dsimp,
      simp only [←tensor_comp, category.comp_id, ←sum_tensor, ←tensor_id, is_bilimit.total i],
    end } } }

variables [has_finite_biproducts C]

/-- The isomorphism showing how tensor product on the left distributes over direct sums. -/
def left_distributor {J : Type} [fintype J] (X : C) (f : J → C) :
  X ⊗ (⨁ f) ≅ ⨁ (λ j, X ⊗ f j) :=
(tensor_left X).map_biproduct f

@[simp]
lemma left_distributor_hom {J : Type} [fintype J] (X : C) (f : J → C) :
  (left_distributor X f).hom = ∑ j : J, (𝟙 X ⊗ biproduct.π f j) ≫ biproduct.ι _ j :=
begin
  ext, dsimp [tensor_left, left_distributor],
  simp [preadditive.sum_comp, biproduct.ι_π, comp_dite],
end

@[simp]
lemma left_distributor_inv {J : Type} [fintype J] (X : C) (f : J → C) :
  (left_distributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (𝟙 X ⊗ biproduct.ι f j) :=
begin
  ext, dsimp [tensor_left, left_distributor],
  simp [preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp],
end

lemma left_distributor_assoc {J : Type} [fintype J] (X Y : C) (f : J → C) :
   (as_iso (𝟙 X) ⊗ left_distributor Y f) ≪≫ left_distributor X _ =
     (α_ X Y (⨁ f)).symm ≪≫ left_distributor (X ⊗ Y) f ≪≫ biproduct.map_iso (λ j, α_ X Y _) :=
begin
  ext,
  simp only [category.comp_id,  category.assoc, eq_to_hom_refl,
    iso.trans_hom, iso.symm_hom, as_iso_hom, comp_zero, comp_dite,
    preadditive.sum_comp, preadditive.comp_sum,
    tensor_sum, id_tensor_comp, tensor_iso_hom, left_distributor_hom,
    biproduct.map_iso_hom, biproduct.ι_map, biproduct.ι_π,
    finset.sum_dite_irrel, finset.sum_dite_eq', finset.sum_const_zero],
  simp only [←id_tensor_comp, biproduct.ι_π],
  simp only [id_tensor_comp, tensor_dite, comp_dite],
  simp only [category.comp_id, comp_zero, monoidal_preadditive.tensor_zero, eq_to_hom_refl,
    tensor_id, if_true, dif_ctx_congr, finset.sum_congr, finset.mem_univ, finset.sum_dite_eq'],
  simp only [←tensor_id, associator_naturality, iso.inv_hom_id_assoc],
end

/-- The isomorphism showing how tensor product on the right distributes over direct sums. -/
def right_distributor {J : Type} [fintype J] (X : C) (f : J → C) :
  (⨁ f) ⊗ X ≅ ⨁ (λ j, f j ⊗ X)  :=
(tensor_right X).map_biproduct f

@[simp]
lemma right_distributor_hom {J : Type} [fintype J] (X : C) (f : J → C) :
  (right_distributor X f).hom = ∑ j : J, (biproduct.π f j ⊗ 𝟙 X) ≫ biproduct.ι _ j :=
begin
  ext, dsimp [tensor_right, right_distributor],
  simp [preadditive.sum_comp, biproduct.ι_π, comp_dite],
end

@[simp]
lemma right_distributor_inv {J : Type} [fintype J] (X : C) (f : J → C) :
  (right_distributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ⊗ 𝟙 X) :=
begin
  ext, dsimp [tensor_right, right_distributor],
  simp [preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp],
end

lemma right_distributor_assoc {J : Type} [fintype J] (X Y : C) (f : J → C) :
   (right_distributor X f ⊗ as_iso (𝟙 Y)) ≪≫ right_distributor Y _ =
     α_ (⨁ f) X Y ≪≫ right_distributor (X ⊗ Y) f ≪≫ biproduct.map_iso (λ j, (α_ _ X Y).symm) :=
begin
  ext,
  simp only [category.comp_id, category.assoc, eq_to_hom_refl, iso.symm_hom,
    iso.trans_hom, as_iso_hom, comp_zero, comp_dite, preadditive.sum_comp, preadditive.comp_sum,
    sum_tensor, comp_tensor_id, tensor_iso_hom, right_distributor_hom,
    biproduct.map_iso_hom, biproduct.ι_map, biproduct.ι_π,
    finset.sum_dite_irrel, finset.sum_dite_eq', finset.sum_const_zero, finset.mem_univ, if_true],
  simp only [←comp_tensor_id, biproduct.ι_π, dite_tensor, comp_dite],
  simp only [category.comp_id, comp_tensor_id, eq_to_hom_refl, tensor_id, comp_zero,
    monoidal_preadditive.zero_tensor,
    if_true, dif_ctx_congr, finset.mem_univ, finset.sum_congr, finset.sum_dite_eq'],
  simp only [←tensor_id, associator_inv_naturality, iso.hom_inv_id_assoc]
end

lemma left_distributor_right_distributor_assoc
  {J : Type*} [fintype J] (X Y : C) (f : J → C) :
  (left_distributor X f ⊗ as_iso (𝟙 Y)) ≪≫ right_distributor Y _ =
    α_ X (⨁ f) Y ≪≫ (as_iso (𝟙 X) ⊗ right_distributor Y _) ≪≫ left_distributor X _ ≪≫
      biproduct.map_iso (λ j, (α_ _ _ _).symm) :=
begin
  ext,
  simp only [category.comp_id, category.assoc, eq_to_hom_refl, iso.symm_hom,
    iso.trans_hom, as_iso_hom, comp_zero, comp_dite, preadditive.sum_comp, preadditive.comp_sum,
    sum_tensor, tensor_sum, comp_tensor_id, tensor_iso_hom,
    left_distributor_hom, right_distributor_hom,
    biproduct.map_iso_hom, biproduct.ι_map, biproduct.ι_π,
    finset.sum_dite_irrel, finset.sum_dite_eq', finset.sum_const_zero, finset.mem_univ, if_true],
  simp only [←comp_tensor_id, ←id_tensor_comp_assoc, category.assoc, biproduct.ι_π,
    comp_dite, dite_comp, tensor_dite, dite_tensor],
  simp only [category.comp_id, category.id_comp, category.assoc, id_tensor_comp,
    comp_zero, zero_comp, monoidal_preadditive.tensor_zero, monoidal_preadditive.zero_tensor,
    comp_tensor_id, eq_to_hom_refl, tensor_id,
    if_true, dif_ctx_congr, finset.sum_congr, finset.mem_univ, finset.sum_dite_eq'],
  simp only [associator_inv_naturality, iso.hom_inv_id_assoc]
end

end category_theory
