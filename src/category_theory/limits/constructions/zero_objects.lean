/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.zero_morphisms
import category_theory.limits.constructions.binary_products

/-!
# Limits involving zero objects

Binary products and coproducts with a zero object always exist,
and pullbacks/pushouts over a zero object are products/coproducts.
-/

noncomputable theory

open category_theory

variables {C : Type*} [category C]

namespace category_theory.limits

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/-- The limit cone for the product with a zero object. -/
def binary_fan_zero_left (X : C) : binary_fan (0 : C) X :=
binary_fan.mk 0 (𝟙 X)

/-- The limit cone for the product with a zero object is limiting. -/
def binary_fan_zero_left_is_limit (X : C) : is_limit (binary_fan_zero_left X) :=
binary_fan.is_limit_mk (λ s, binary_fan.snd s) (by tidy) (by tidy) (by tidy)

instance has_binary_product_zero_left (X : C) : has_binary_product (0 : C) X :=
has_limit.mk ⟨_, binary_fan_zero_left_is_limit X⟩

/-- A zero object is a left unit for categorical product. -/
def zero_prod_iso (X : C) : (0 : C) ⨯ X ≅ X :=
limit.iso_limit_cone ⟨_, binary_fan_zero_left_is_limit X⟩

@[simp] lemma zero_prod_iso_hom (X : C) : (zero_prod_iso X).hom = prod.snd :=
rfl
@[simp] lemma zero_prod_iso_inv_snd (X : C) : (zero_prod_iso X).inv ≫ prod.snd = 𝟙 X :=
by { dsimp [zero_prod_iso, binary_fan_zero_left], simp, }

/-- The limit cone for the product with a zero object. -/
def binary_fan_zero_right (X : C) : binary_fan X (0 : C) :=
binary_fan.mk (𝟙 X) 0

/-- The limit cone for the product with a zero object is limiting. -/
def binary_fan_zero_right_is_limit (X : C) : is_limit (binary_fan_zero_right X) :=
binary_fan.is_limit_mk (λ s, binary_fan.fst s) (by tidy) (by tidy) (by tidy)

instance has_binary_product_zero_right (X : C) : has_binary_product X (0 : C) :=
has_limit.mk ⟨_, binary_fan_zero_right_is_limit X⟩

/-- A zero object is a right unit for categorical product. -/
def prod_zero_iso (X : C) : X ⨯ (0 : C) ≅ X :=
limit.iso_limit_cone ⟨_, binary_fan_zero_right_is_limit X⟩

@[simp] lemma prod_zero_iso_hom (X : C) : (prod_zero_iso X).hom = prod.fst :=
rfl
@[simp] lemma prod_zero_iso_iso_inv_snd (X : C) : (prod_zero_iso X).inv ≫ prod.fst = 𝟙 X :=
by { dsimp [prod_zero_iso, binary_fan_zero_right], simp, }

/-- The colimit cocone for the coproduct with a zero object. -/
def binary_cofan_zero_left (X : C) : binary_cofan (0 : C) X :=
binary_cofan.mk 0 (𝟙 X)

/-- The colimit cocone for the coproduct with a zero object is colimiting. -/
def binary_cofan_zero_left_is_colimit (X : C) : is_colimit (binary_cofan_zero_left X) :=
binary_cofan.is_colimit_mk (λ s, binary_cofan.inr s) (by tidy) (by tidy) (by tidy)

instance has_binary_coproduct_zero_left (X : C) : has_binary_coproduct (0 : C) X :=
has_colimit.mk ⟨_, binary_cofan_zero_left_is_colimit X⟩

/-- A zero object is a left unit for categorical coproduct. -/
def zero_coprod_iso (X : C) : (0 : C) ⨿ X ≅ X :=
colimit.iso_colimit_cocone ⟨_, binary_cofan_zero_left_is_colimit X⟩

@[simp] lemma inr_zero_coprod_iso_hom (X : C) : coprod.inr ≫ (zero_coprod_iso X).hom = 𝟙 X :=
by { dsimp [zero_coprod_iso, binary_cofan_zero_left], simp, }
@[simp] lemma zero_coprod_iso_inv (X : C) : (zero_coprod_iso X).inv = coprod.inr :=
rfl

/-- The colimit cocone for the coproduct with a zero object. -/
def binary_cofan_zero_right (X : C) : binary_cofan X (0 : C) :=
binary_cofan.mk (𝟙 X) 0

/-- The colimit cocone for the coproduct with a zero object is colimiting. -/
def binary_cofan_zero_right_is_colimit (X : C) : is_colimit (binary_cofan_zero_right X) :=
binary_cofan.is_colimit_mk (λ s, binary_cofan.inl s) (by tidy) (by tidy) (by tidy)

instance has_binary_coproduct_zero_right (X : C) : has_binary_coproduct X (0 : C) :=
has_colimit.mk ⟨_, binary_cofan_zero_right_is_colimit X⟩

/-- A zero object is a right unit for categorical coproduct. -/
def coprod_zero_iso (X : C) : X ⨿ (0 : C) ≅ X :=
colimit.iso_colimit_cocone ⟨_, binary_cofan_zero_right_is_colimit X⟩

@[simp] lemma inr_coprod_zeroiso_hom (X : C) : coprod.inl ≫ (coprod_zero_iso X).hom = 𝟙 X :=
by { dsimp [coprod_zero_iso, binary_cofan_zero_right], simp, }
@[simp] lemma coprod_zero_iso_inv (X : C) : (coprod_zero_iso X).inv = coprod.inl :=
rfl

instance has_pullback_over_zero
  (X Y : C) [has_binary_product X Y] : has_pullback (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
has_limit.mk ⟨_, is_pullback_of_is_terminal_is_product _ _ _ _
  has_zero_object.zero_is_terminal (prod_is_prod X Y)⟩

/-- The pullback over the zeron object is the product. -/
def pullback_zero_zero_iso (X Y : C) [has_binary_product X Y] :
  pullback (0 : X ⟶ 0) (0 : Y ⟶ 0) ≅ X ⨯ Y :=
limit.iso_limit_cone ⟨_, is_pullback_of_is_terminal_is_product _ _ _ _
  has_zero_object.zero_is_terminal (prod_is_prod X Y)⟩

@[simp] lemma pullback_zero_zero_iso_inv_fst (X Y : C) [has_binary_product X Y] :
  (pullback_zero_zero_iso X Y).inv ≫ pullback.fst = prod.fst :=
by { dsimp [pullback_zero_zero_iso], simp, }
@[simp] lemma pullback_zero_zero_iso_inv_snd (X Y : C) [has_binary_product X Y] :
  (pullback_zero_zero_iso X Y).inv ≫ pullback.snd = prod.snd :=
by { dsimp [pullback_zero_zero_iso], simp, }
@[simp] lemma pullback_zero_zero_iso_hom_fst (X Y : C) [has_binary_product X Y] :
  (pullback_zero_zero_iso X Y).hom ≫ prod.fst = pullback.fst :=
by { simp [←iso.eq_inv_comp], }
@[simp] lemma pullback_zero_zero_iso_hom_snd (X Y : C) [has_binary_product X Y] :
  (pullback_zero_zero_iso X Y).hom ≫ prod.snd = pullback.snd :=
by { simp [←iso.eq_inv_comp], }

instance has_pushout_over_zero
  (X Y : C) [has_binary_coproduct X Y] : has_pushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) :=
has_colimit.mk ⟨_, is_pushout_of_is_initial_is_coproduct _ _ _ _
  has_zero_object.zero_is_initial (coprod_is_coprod X Y)⟩

/-- The pushout over the zero object is the coproduct. -/
def pushout_zero_zero_iso
  (X Y : C) [has_binary_coproduct X Y] : pushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) ≅ X ⨿ Y :=
colimit.iso_colimit_cocone ⟨_, is_pushout_of_is_initial_is_coproduct _ _ _ _
  has_zero_object.zero_is_initial (coprod_is_coprod X Y)⟩

@[simp] lemma inl_pushout_zero_zero_iso_hom (X Y : C) [has_binary_coproduct X Y] :
  pushout.inl ≫ (pushout_zero_zero_iso X Y).hom = coprod.inl :=
by { dsimp [pushout_zero_zero_iso], simp, }
@[simp] lemma inr_pushout_zero_zero_iso_hom (X Y : C) [has_binary_coproduct X Y] :
  pushout.inr ≫ (pushout_zero_zero_iso X Y).hom = coprod.inr :=
by { dsimp [pushout_zero_zero_iso], simp, }
@[simp] lemma inl_pushout_zero_zero_iso_inv (X Y : C) [has_binary_coproduct X Y] :
  coprod.inl ≫ (pushout_zero_zero_iso X Y).inv = pushout.inl :=
by { simp [iso.comp_inv_eq], }
@[simp] lemma inr_pushout_zero_zero_iso_inv (X Y : C) [has_binary_coproduct X Y] :
  coprod.inr ≫ (pushout_zero_zero_iso X Y).inv = pushout.inr :=
by { simp [iso.comp_inv_eq], }

end category_theory.limits
