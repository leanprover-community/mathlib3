/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.monoidal.free.coherence
import category_theory.isomorphism_classes

universes v u
noncomputable theory

namespace category_theory
open monoidal_category free_monoidal_category

variables {C : Type u} [category.{v} C] [monoidal_category C]

local notation `F` := free_monoidal_category
local infixr ` ⟶ᵐ `:10 := hom

lemma is_isomorphic.tensor {W X Y Z : C} :
  is_isomorphic W X → is_isomorphic Y Z → is_isomorphic (W ⊗ Y) (X ⊗ Z) :=
λ ⟨α⟩ ⟨β⟩, ⟨α ⊗ β⟩

local infixr ` =ᵐ `:50 := is_isomorphic
local notation X ` ∼ `:50 X' := X = (project id).obj X'

def hom_of_monoidal_eq {X Y : F C} (h : X =ᵐ Y) : (project id).obj X ⟶ (project id).obj Y :=
(project id).map (classical.choice h).hom

lemma hom_of_monoidal_eq_eq {X Y : F C} {h : X =ᵐ Y} (h' : X ⟶ Y) :
  hom_of_monoidal_eq h = (project id).map h' :=
by { dsimp only [hom_of_monoidal_eq], congr' 1 }

def coherent_comp {W X Y Z : C} {X' Y' : F C} (h : X' =ᵐ Y') (hX : X ∼ X')
  (hY : Y ∼ Y') (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
f ≫ eq_to_hom hX ≫ hom_of_monoidal_eq h ≫ eq_to_hom hY.symm ≫ g

notation f ` ≫ᵐ[`:80 h:80 `] `:0 g:80 := coherent_comp h (by assumption) (by assumption) f g
infixr ` ≫ᵐ `:80 := coherent_comp _ _ _

lemma coherent_comp_constructor {W X Y Z : C} {X' Y' : F C} (f : W ⟶ X) (g : Y ⟶ Z)
  (h : X' ≅ Y') (hX : X ∼ X') (hY : Y ∼ Y') :
  f ≫ᵐ[⟨h⟩] g = f ≫ eq_to_hom hX ≫ (project id).map h.hom ≫ eq_to_hom hY.symm ≫ g :=
by rw [coherent_comp, hom_of_monoidal_eq_eq h.hom]

lemma comp_eq_coherent_comp {X Y Z : C} (Y' : F C)
  (h : Y ∼ Y' . tactic.assumption) (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = f ≫ᵐ[⟨as_iso (𝟙 _)⟩] g :=
by simp [coherent_comp_constructor]

mk_simp_attribute coherent_simps "Some nice text here"

@[simp, coherent_simps] lemma coherent_assoc {U V W X Y Z : C} {V' W' X' Y' : F C}
  (f : U ⟶ V) {h : V' =ᵐ W'} (g : W ⟶ X) {h' : X' =ᵐ Y'} (i : Y ⟶ Z) (hV : V ∼ V')
  (hW : W ∼ W') (hX : X ∼ X') (hY : Y ∼ Y') :
  (f ≫ᵐ[h] g) ≫ᵐ[h'] i = f ≫ᵐ[h] (g ≫ᵐ[h'] i) :=
by { unfreezingI { rcases h, rcases h' }, simp [coherent_comp_constructor] }

@[simp, coherent_simps] lemma coherent_comp_id_coherent_comp {V W X Y Z : C} {W' X' Y' : F C}
  (f : V ⟶ W) {h : W' =ᵐ X'} {h' : X' =ᵐ Y'} (g : Y ⟶ Z) (hW : W ∼ W') (hX : X ∼ X') (hY : Y ∼ Y') :
  f ≫ᵐ[h] 𝟙 X ≫ᵐ[h'] g = f ≫ᵐ[h.trans h'] g :=
begin
  unfreezingI { cases h, cases h' },
  simp only [coherent_comp, hom_of_monoidal_eq_eq h.hom, hom_of_monoidal_eq_eq h'.hom,
    hom_of_monoidal_eq_eq (h.hom ≫ h'.hom), category.id_comp, eq_to_hom_refl,
    eq_to_hom_trans_assoc, functor.map_comp, category.assoc]
end

@[simp, coherent_simps] lemma coherent_comp_id_coherent_comp' {V W : C} (X : C) {Y Z : C}
  {W' X' Y' : F C} (f : V ⟶ W) {h : W' =ᵐ X'} {h' : X' =ᵐ Y'} (g : Y ⟶ Z) (hW : W ∼ W')
  (hX : X ∼ X') (hY : Y ∼ Y') : f ≫ᵐ[h] (𝟙 X ≫ᵐ[h'] g) = f ≫ᵐ[h.trans h'] g :=
by rw [←coherent_assoc, coherent_comp_id_coherent_comp]
lemma α_hom_eq_id_coherent_comp_id {X Y Z : C} {X' Y' Z' : F C} (hX : X ∼ X' . tactic.assumption)
  (hY : Y ∼ Y' . tactic.assumption) (hZ : Z ∼ Z' . tactic.assumption)
  (hXYZ : ((X ⊗ Y) ⊗ Z) ∼ ((X' ⊗ Y') ⊗ Z') . tactic.assumption)
  (hXYZ' : (X ⊗ Y ⊗ Z) ∼ (X' ⊗ Y' ⊗ Z') . tactic.assumption) :
  (α_ X Y Z).hom = 𝟙 ((X ⊗ Y) ⊗ Z) ≫ᵐ[⟨as_iso ⟦hom.α_hom X' Y' Z'⟧⟩] 𝟙 (X ⊗ Y ⊗ Z) :=
begin
  rw coherent_comp_constructor,
  dsimp [project, project_map, project_map_aux, -mk_α_hom],
  cases hX, cases hY, cases hZ,
  simp only [project_map_aux, category.id_comp, eq_to_hom_refl, category.comp_id]
end

lemma α_inv_eq_id_coherent_comp_id {X Y Z : C} {X' Y' Z' : F C} (hX : X ∼ X' . tactic.assumption)
  (hY : Y ∼ Y' . tactic.assumption) (hZ : Z ∼ Z' . tactic.assumption)
  (hXYZ : ((X ⊗ Y) ⊗ Z) ∼ ((X' ⊗ Y') ⊗ Z') . tactic.assumption)
  (hXYZ' : (X ⊗ Y ⊗ Z) ∼ (X' ⊗ Y' ⊗ Z') . tactic.assumption) :
  (α_ X Y Z).inv = 𝟙 (X ⊗ Y ⊗ Z) ≫ᵐ[⟨as_iso ⟦hom.α_inv X' Y' Z'⟧⟩] 𝟙 ((X ⊗ Y) ⊗ Z) :=
begin
  rw coherent_comp_constructor,
  dsimp [project, project_map, project_map_aux, -mk_α_inv],
  cases hX, cases hY, cases hZ,
  simp only [project_map_aux, category.id_comp, eq_to_hom_refl, category.comp_id]
end

lemma ρ_hom_eq_id_coherent_comp_id {X : C} {X' : F C} (hX : X ∼ X' . tactic.assumption)
  (hX' : X ⊗ 𝟙_ C ∼ X' ⊗ 𝟙_ (F C) . tactic.assumption) :
  (ρ_ X).hom = 𝟙 (X ⊗ 𝟙_ C) ≫ᵐ[⟨as_iso ⟦hom.ρ_hom X'⟧⟩] 𝟙 X :=
begin
  rw coherent_comp_constructor,
  dsimp [project, project_map, project_map_aux, -mk_ρ_hom],
  cases hX,
  simp only [category.id_comp, eq_to_hom_refl, category.comp_id]
end

-- Next step: get rid of the composite ∼ assumptions

end category_theory
