/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.preserves.shapes.pullbacks
import category_theory.limits.preserves.shapes.terminal

/-!
# Constructing binary product from pullbacks and terminal object.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The product is the pullback over the terminal objects. In particular, if a category
has pullbacks and a terminal object, then it has binary products.

We also provide the dual.
-/

universes v v' u u'

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D] (F : C ⥤ D)

/-- If a span is the pullback span over the terminal object, then it is a binary product. -/
def is_binary_product_of_is_terminal_is_pullback (F : discrete walking_pair ⥤ C) (c : cone F)
  {X : C} (hX : is_terminal X)
  (f : F.obj ⟨walking_pair.left⟩ ⟶ X) (g : F.obj ⟨walking_pair.right⟩ ⟶ X)
  (hc : is_limit (pullback_cone.mk (c.π.app ⟨walking_pair.left⟩) (c.π.app ⟨walking_pair.right⟩ : _)
    $ hX.hom_ext (_ ≫ f) (_ ≫ g))) : is_limit c :=
{ lift := λ s, hc.lift
    (pullback_cone.mk (s.π.app ⟨walking_pair.left⟩) (s.π.app ⟨walking_pair.right⟩)
      (hX.hom_ext _ _)),
  fac' := λ s j, discrete.cases_on j
    (λ j, walking_pair.cases_on j (hc.fac _ walking_cospan.left) (hc.fac _ walking_cospan.right)),
  uniq' := λ s m J,
    begin
      let c' := pullback_cone.mk
        (m ≫ c.π.app ⟨walking_pair.left⟩) (m ≫ c.π.app ⟨walking_pair.right⟩ : _)
        (hX.hom_ext (_ ≫ f) (_ ≫ g)),
      rw [←J, ←J],
      apply hc.hom_ext,
      rintro (_|(_|_)); simp only [pullback_cone.mk_π_app_one, pullback_cone.mk_π_app],
      exacts [(category.assoc _ _ _).symm.trans (hc.fac_assoc c' walking_cospan.left f).symm,
        (hc.fac c' walking_cospan.left).symm, (hc.fac c' walking_cospan.right).symm]
    end }

/-- The pullback over the terminal object is the product -/
def is_product_of_is_terminal_is_pullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X)
  (k : W ⟶ Y) (H₁ : is_terminal Z)
  (H₂ : is_limit (pullback_cone.mk _ _ (show h ≫ f = k ≫ g, from H₁.hom_ext _ _))) :
  is_limit (binary_fan.mk h k) :=
begin
  apply is_binary_product_of_is_terminal_is_pullback _ _ H₁,
  exact H₂
end

/-- The product is the pullback over the terminal object. -/
def is_pullback_of_is_terminal_is_product {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X)
  (k : W ⟶ Y) (H₁ : is_terminal Z)
  (H₂ : is_limit (binary_fan.mk h k)) :
  is_limit (pullback_cone.mk _ _ (show h ≫ f = k ≫ g, from H₁.hom_ext _ _)) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  use H₂.lift (binary_fan.mk s.fst s.snd),
  use H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.left⟩,
  use H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.right⟩,
  intros m h₁ h₂,
  apply H₂.hom_ext,
  rintro ⟨⟨⟩⟩,
  { exact h₁.trans (H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.left⟩).symm },
  { exact h₂.trans (H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.right⟩).symm }
end

/-- Any category with pullbacks and a terminal object has a limit cone for each walking pair. -/
noncomputable def limit_cone_of_terminal_and_pullbacks [has_terminal C] [has_pullbacks C]
  (F : discrete walking_pair ⥤ C) : limit_cone F :=
{ cone :=
  { X := pullback (terminal.from (F.obj ⟨walking_pair.left⟩))
                  (terminal.from (F.obj ⟨walking_pair.right⟩)),
    π := discrete.nat_trans (λ x, discrete.cases_on x
      (λ x, walking_pair.cases_on x pullback.fst pullback.snd)) },
  is_limit := is_binary_product_of_is_terminal_is_pullback
    F _ terminal_is_terminal _ _ (pullback_is_pullback _ _) }

variable (C)

/-- Any category with pullbacks and terminal object has binary products. -/
-- This is not an instance, as it is not always how one wants to construct binary products!
lemma has_binary_products_of_has_terminal_and_pullbacks
  [has_terminal C] [has_pullbacks C] :
  has_binary_products C :=
{ has_limit := λ F, has_limit.mk (limit_cone_of_terminal_and_pullbacks F) }

variable {C}

/-- A functor that preserves terminal objects and pullbacks preserves binary products. -/
noncomputable
def preserves_binary_products_of_preserves_terminal_and_pullbacks
  [has_terminal C] [has_pullbacks C]
  [preserves_limits_of_shape (discrete.{0} pempty) F]
  [preserves_limits_of_shape walking_cospan F] :
  preserves_limits_of_shape (discrete walking_pair) F :=
⟨λ K, preserves_limit_of_preserves_limit_cone (limit_cone_of_terminal_and_pullbacks K).2
begin
  apply is_binary_product_of_is_terminal_is_pullback _ _
    (is_limit_of_has_terminal_of_preserves_limit F),
  apply is_limit_of_has_pullback_of_preserves_limit,
end⟩

/-- In a category with a terminal object and pullbacks,
a product of objects `X` and `Y` is isomorphic to a pullback. -/
noncomputable
def prod_iso_pullback [has_terminal C] [has_pullbacks C] (X Y : C) [has_binary_product X Y] :
  X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
limit.iso_limit_cone (limit_cone_of_terminal_and_pullbacks _)

/-- If a cospan is the pushout cospan under the initial object, then it is a binary coproduct. -/
def is_binary_coproduct_of_is_initial_is_pushout (F : discrete walking_pair ⥤ C) (c : cocone F)
  {X : C} (hX : is_initial X)
  (f : X ⟶ F.obj ⟨walking_pair.left⟩) (g : X ⟶ F.obj ⟨walking_pair.right⟩)
  (hc : is_colimit (pushout_cocone.mk (c.ι.app ⟨walking_pair.left⟩)
    (c.ι.app ⟨walking_pair.right⟩ : _) $ hX.hom_ext (f ≫ _) (g ≫ _))) : is_colimit c :=
{ desc := λ s, hc.desc
    (pushout_cocone.mk (s.ι.app ⟨walking_pair.left⟩) (s.ι.app ⟨walking_pair.right⟩)
      (hX.hom_ext _ _)),
  fac' := λ s j, discrete.cases_on j
    (λ j, walking_pair.cases_on j (hc.fac _ walking_span.left) (hc.fac _ walking_span.right)),
  uniq' := λ s m J,
    begin
      let c' := pushout_cocone.mk
        (c.ι.app ⟨walking_pair.left⟩ ≫ m) (c.ι.app ⟨walking_pair.right⟩ ≫ m)
        (hX.hom_ext (f ≫ _) (g ≫ _)),
      rw [←J, ←J],
      apply hc.hom_ext,
      rintro (_|(_|_));
        simp only [pushout_cocone.mk_ι_app_zero, pushout_cocone.mk_ι_app, category.assoc],
      congr' 1,
      exacts [(hc.fac c' walking_span.left).symm,
        (hc.fac c' walking_span.left).symm, (hc.fac c' walking_span.right).symm]
    end }

/-- The pushout under the initial object is the coproduct -/
def is_coproduct_of_is_initial_is_pushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X)
  (k : W ⟶ Y) (H₁ : is_initial W)
  (H₂ : is_colimit (pushout_cocone.mk _ _ (show h ≫ f = k ≫ g, from H₁.hom_ext _ _))) :
  is_colimit (binary_cofan.mk f g) :=
begin
  apply is_binary_coproduct_of_is_initial_is_pushout _ _ H₁,
  exact H₂
end

/-- The coproduct is the pushout under the initial object. -/
def is_pushout_of_is_initial_is_coproduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X)
  (k : W ⟶ Y) (H₁ : is_initial W)
  (H₂ : is_colimit (binary_cofan.mk f g)) :
  is_colimit (pushout_cocone.mk _ _ (show h ≫ f = k ≫ g, from H₁.hom_ext _ _)) :=
begin
  apply pushout_cocone.is_colimit_aux',
  intro s,
  use H₂.desc (binary_cofan.mk s.inl s.inr),
  use H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.left⟩,
  use H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.right⟩,
  intros m h₁ h₂,
  apply H₂.hom_ext,
  rintro ⟨⟨⟩⟩,
  { exact h₁.trans (H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.left⟩).symm },
  { exact h₂.trans (H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.right⟩).symm }
end

/-- Any category with pushouts and an initial object has a colimit cocone for each walking pair. -/
noncomputable def colimit_cocone_of_initial_and_pushouts [has_initial C] [has_pushouts C]
  (F : discrete walking_pair ⥤ C) : colimit_cocone F :=
{ cocone :=
  { X := pushout (initial.to (F.obj ⟨walking_pair.left⟩))
                  (initial.to (F.obj ⟨walking_pair.right⟩)),
    ι := discrete.nat_trans (λ x, discrete.cases_on x
      (λ x, walking_pair.cases_on x pushout.inl pushout.inr)) },
  is_colimit := is_binary_coproduct_of_is_initial_is_pushout
    F _ initial_is_initial _ _ (pushout_is_pushout _ _) }


variable (C)

/-- Any category with pushouts and initial object has binary coproducts. -/
-- This is not an instance, as it is not always how one wants to construct binary coproducts!
lemma has_binary_coproducts_of_has_initial_and_pushouts
  [has_initial C] [has_pushouts C] :
  has_binary_coproducts C :=
{ has_colimit := λ F, has_colimit.mk (colimit_cocone_of_initial_and_pushouts F) }

variable {C}

/-- A functor that preserves initial objects and pushouts preserves binary coproducts. -/
noncomputable
def preserves_binary_coproducts_of_preserves_initial_and_pushouts
  [has_initial C] [has_pushouts C]
  [preserves_colimits_of_shape (discrete.{0} pempty) F]
  [preserves_colimits_of_shape walking_span F] :
  preserves_colimits_of_shape (discrete walking_pair) F :=
⟨λ K, preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_of_initial_and_pushouts K).2
begin
  apply is_binary_coproduct_of_is_initial_is_pushout _ _
    (is_colimit_of_has_initial_of_preserves_colimit F),
  apply is_colimit_of_has_pushout_of_preserves_colimit,
end⟩


/-- In a category with an initial object and pushouts,
a coproduct of objects `X` and `Y` is isomorphic to a pushout. -/
noncomputable
def coprod_iso_pushout [has_initial C] [has_pushouts C] (X Y : C) [has_binary_coproduct X Y] :
  X ⨿ Y ≅ pushout (initial.to X) (initial.to Y) :=
colimit.iso_colimit_cocone (colimit_cocone_of_initial_and_pushouts _)
