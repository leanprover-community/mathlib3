/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products

/-!
# Constructing binary product from pullbacks and terminal object.

The product is the pullback over the terminal objects. In particular, if a category
has pullbacks and a terminal object, then it has binary products.

We also provide the dual.
-/

universes v u

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C]

/-- The pullback over the terminal object is the product -/
def is_product_of_is_terminal_is_pullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X)
  (k : W ⟶ Y) (H₁ : is_terminal Z)
  (H₂ : is_limit (pullback_cone.mk _ _ (show h ≫ f = k ≫ g, from H₁.hom_ext _ _))) :
  is_limit (binary_fan.mk h k) :=
{ lift := λ c, H₂.lift (pullback_cone.mk
    (c.π.app ⟨walking_pair.left⟩) (c.π.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _)),
  fac' := λ c j,
  begin
    cases j,
    convert H₂.fac (pullback_cone.mk (c.π.app ⟨walking_pair.left⟩)
      (c.π.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _)) (some j) using 1,
    rcases j; refl,
  end,
  uniq' := λ c m hm,
  begin
    apply pullback_cone.is_limit.hom_ext H₂,
    { exact (hm ⟨walking_pair.left⟩).trans (H₂.fac (pullback_cone.mk (c.π.app ⟨walking_pair.left⟩)
        (c.π.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _)) walking_cospan.left).symm },
    { exact (hm ⟨walking_pair.right⟩).trans (H₂.fac (pullback_cone.mk (c.π.app ⟨walking_pair.left⟩)
        (c.π.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _)) walking_cospan.right).symm },
  end }

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
  is_limit :=
  { lift := λ c, pullback.lift ((c.π).app ⟨walking_pair.left⟩)
                                ((c.π).app ⟨walking_pair.right⟩)
                                (subsingleton.elim _ _),
    fac' := λ s c, discrete.cases_on c
      (λ c, walking_pair.cases_on c (limit.lift_π _ _) (limit.lift_π _ _)),
    uniq' := λ s m J,
              begin
                rw [←J, ←J],
                ext;
                rw limit.lift_π;
                refl
              end } }

variable (C)

/-- Any category with pullbacks and terminal object has binary products. -/
-- This is not an instance, as it is not always how one wants to construct binary products!
lemma has_binary_products_of_terminal_and_pullbacks
  [has_terminal C] [has_pullbacks C] :
  has_binary_products C :=
{ has_limit := λ F, has_limit.mk (limit_cone_of_terminal_and_pullbacks F) }

/-- In a category with a terminal object and pullbacks,
a product of objects `X` and `Y` is isomorphic to a pullback. -/
noncomputable
def prod_iso_pullback [has_terminal C] [has_pullbacks C] (X Y : C) [has_binary_product X Y] :
  X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
limit.iso_limit_cone (limit_cone_of_terminal_and_pullbacks _)

variable {C}

/-- The pushout under the initial object is the coproduct -/
def is_coproduct_of_is_initial_is_pushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X)
  (k : W ⟶ Y) (H₁ : is_initial W)
  (H₂ : is_colimit (pushout_cocone.mk _ _ (show h ≫ f = k ≫ g, from H₁.hom_ext _ _))) :
  is_colimit (binary_cofan.mk f g) :=
{ desc := λ c, H₂.desc (pushout_cocone.mk
    (c.ι.app ⟨walking_pair.left⟩) (c.ι.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _)),
  fac' := λ c j,
  begin
    cases j,
    convert H₂.fac (pushout_cocone.mk (c.ι.app ⟨walking_pair.left⟩) (c.ι.app ⟨walking_pair.right⟩)
      (H₁.hom_ext _ _)) (some j) using 1,
    cases j; refl
  end,
  uniq' := λ c m hm,
  begin
    apply pushout_cocone.is_colimit.hom_ext H₂,
    { exact (hm ⟨walking_pair.left⟩).trans (H₂.fac (pushout_cocone.mk (c.ι.app ⟨walking_pair.left⟩)
        (c.ι.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _)) walking_cospan.left).symm },
    { exact (hm ⟨walking_pair.right⟩).trans (H₂.fac (pushout_cocone.mk (c.ι.app ⟨walking_pair.left⟩)
        (c.ι.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _)) walking_cospan.right).symm },
  end }

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
  is_colimit :=
  { desc := λ c, pushout.desc (c.ι.app ⟨walking_pair.left⟩)
                              (c.ι.app ⟨walking_pair.right⟩)
                              (subsingleton.elim _ _),
    fac' := λ s c, discrete.cases_on c
      (λ c, walking_pair.cases_on c (colimit.ι_desc _ _) (colimit.ι_desc _ _)),
    uniq' := λ s m J,
              begin
                rw [←J, ←J],
                ext;
                rw colimit.ι_desc;
                refl
              end } }

variable (C)

/-- Any category with pushouts and initial object has binary coproducts. -/
-- This is not an instance, as it is not always how one wants to construct binary coproducts!
lemma has_binary_coproducts_of_initial_and_pushouts
  [has_initial C] [has_pushouts C] :
  has_binary_coproducts C :=
{ has_colimit := λ F, has_colimit.mk (colimit_cocone_of_initial_and_pushouts F) }

/-- In a category with an initial object and pushouts,
a coproduct of objects `X` and `Y` is isomorphic to a pushout. -/
noncomputable
def coprod_iso_pushout [has_initial C] [has_pushouts C] (X Y : C) [has_binary_coproduct X Y] :
  X ⨿ Y ≅ pushout (initial.to X) (initial.to Y) :=
colimit.iso_colimit_cocone (colimit_cocone_of_initial_and_pushouts _)
