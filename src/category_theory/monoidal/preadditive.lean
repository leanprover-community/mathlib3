/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.additive_functor
import category_theory.monoidal.category

/-!
# Preadditive monoidal categories

A monoidal category is `monoidal_preadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/

noncomputable theory

namespace category_theory

open category_theory.limits
open category_theory.monoidal_category

variables (C : Type*) [category C] [preadditive C] [monoidal_category C]

/--
A category is `monoidal_preadditive` if tensoring is linear in both factors.

Note we don't `extend preadditive C` here, as `abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class monoidal_preadditive :=
(tensor_zero' : ∀ {W X Y Z : C} (f : W ⟶ X), f ⊗ (0 : Y ⟶ Z) = 0 . obviously)
(zero_tensor' : ∀ {W X Y Z : C} (f : Y ⟶ Z), (0 : W ⟶ X) ⊗ f = 0 . obviously)
(tensor_add' : ∀ {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z), f ⊗ (g + h) = f ⊗ g + f ⊗ h . obviously)
(add_tensor' : ∀ {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z), (f + g) ⊗ h = f ⊗ h + g ⊗ h . obviously)

restate_axiom monoidal_preadditive.tensor_zero'
restate_axiom monoidal_preadditive.zero_tensor'
restate_axiom monoidal_preadditive.tensor_add'
restate_axiom monoidal_preadditive.add_tensor'
attribute [simp] monoidal_preadditive.tensor_zero monoidal_preadditive.zero_tensor

variables [monoidal_preadditive C]

local attribute [simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance tensoring_left_additive (X : C) : ((tensoring_left C).obj X).additive := {}
instance tensoring_right_additive (X : C) : ((tensoring_right C).obj X).additive := {}

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

variables {C} [has_finite_biproducts C]

def left_distributor {J : Type*} [decidable_eq J] [fintype J] (X : C) (f : J → C) :
  X ⊗ (⨁ f) ≅ ⨁ (λ j, X ⊗ f j) :=
{ hom := ∑ j : J, (𝟙 X ⊗ biproduct.π f j) ≫ biproduct.ι _ j,
  inv := ∑ j : J, biproduct.π _ j ≫ (𝟙 X ⊗ biproduct.ι f j),
  hom_inv_id' := begin
    simp only [if_true, dif_ctx_congr,
      finset.mem_univ, finset.sum_congr, finset.sum_dite_eq',
      preadditive.sum_comp, preadditive.comp_sum,
      category.id_comp, category.assoc, eq_to_hom_refl,
      biproduct.ι_π_assoc, comp_zero, zero_comp, dite_comp, comp_dite],
    simp only [←id_tensor_comp, ←tensor_sum, biproduct.total, tensor_id],
  end,
  inv_hom_id' := begin
    ext j j',
    simp only [preadditive.sum_comp, preadditive.comp_sum,
      category.assoc, category.comp_id, category.id_comp, dite_comp, comp_dite,
      ←id_tensor_comp_assoc, biproduct.ι_π, biproduct.ι_π_assoc],
    simp only [category.comp_id, category.id_comp, eq_to_hom_refl, tensor_dite,
      finset.sum_dite_eq, finset.mem_univ, finset.sum_congr, finset.sum_dite_eq',
      dite_eq_ite, if_t_t, if_true, dif_ctx_congr,
      comp_zero, zero_comp, monoidal_preadditive.tensor_zero],
    split_ifs with h,
    { cases h, simp, },
    { refl, },
  end, }

def right_distributor {J : Type*} [decidable_eq J] [fintype J] (X : C) (f : J → C) :
  (⨁ f) ⊗ X ≅ ⨁ (λ j, f j ⊗ X) :=
{ hom := ∑ j : J, (biproduct.π f j ⊗ 𝟙 X) ≫ biproduct.ι _ j,
  inv := ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ⊗ 𝟙 X),
  hom_inv_id' := begin
    simp only [if_true, dif_ctx_congr,
      finset.mem_univ, finset.sum_congr, finset.sum_dite_eq',
      preadditive.sum_comp, preadditive.comp_sum,
      category.id_comp, category.assoc, eq_to_hom_refl,
      biproduct.ι_π_assoc, comp_zero, zero_comp, dite_comp, comp_dite],
    simp only [←comp_tensor_id, ←sum_tensor, biproduct.total, tensor_id],
  end,
  inv_hom_id' := begin
    ext j j',
    simp only [preadditive.sum_comp, preadditive.comp_sum,
      category.assoc, category.comp_id, category.id_comp, dite_comp, comp_dite,
      ←comp_tensor_id_assoc, biproduct.ι_π, biproduct.ι_π_assoc],
    simp only [category.comp_id, category.id_comp, eq_to_hom_refl, tensor_dite,
      finset.sum_dite_eq, finset.mem_univ, finset.sum_congr, finset.sum_dite_eq',
      dite_eq_ite, if_t_t, if_true, dif_ctx_congr,
      comp_zero, zero_comp, monoidal_preadditive.tensor_zero],
    split_ifs with h,
    { cases h, simp, },
    { simp, },
  end, }

end category_theory
