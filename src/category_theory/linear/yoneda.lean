/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.basic
import category_theory.linear
import category_theory.preadditive.additive_functor
import category_theory.preadditive.yoneda

/-!
# The Yoneda embedding for `R`-linear categories

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`.

TODO: `linear_yoneda R C` is `R`-linear.
TODO: In fact, `linear_yoneda` itself is additive and `R`-linear.
-/

universes w v u

open opposite

namespace category_theory

variables (R : Type w) [ring R] (C : Type u) [category.{v} C] [preadditive C] [linear R C]

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linear_yoneda : C ⥤ Cᵒᵖ ⥤ Module R :=
{ obj := λ X,
  { obj := λ Y, Module.of R (unop Y ⟶ X),
    map := λ Y Y' f, linear.left_comp R _ f.unop,
    map_comp' := λ _ _ _ f g, begin ext, dsimp, erw [category.assoc] end,
    map_id' := λ Y, begin ext, dsimp, erw [category.id_comp] end },
  map := λ X X' f, { app := λ Y, linear.right_comp R _ f },
  map_id' := λ X, by { ext, simp }, -- `obviously` provides these, but slowly
  map_comp' := λ _ _ _ f g, by { ext, simp } }

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `Y : Cᵒᵖ` to the `Module R`-valued copresheaf on `C`,
with value on `X : C` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linear_coyoneda : Cᵒᵖ ⥤ C ⥤ Module R :=
{ obj := λ Y,
  { obj := λ X, Module.of R (unop Y ⟶ X),
    map := λ Y Y', linear.right_comp _ _,
    map_id' := λ Y, by { ext, exact category.comp_id _ },
    map_comp' := λ _ _ _ f g, by { ext, exact eq.symm (category.assoc _ _ _) } },
  map := λ Y Y' f, { app := λ X, linear.left_comp _ _ f.unop },
  map_id' := λ X, by { ext, simp }, -- `obviously` provides these, but slowly
  map_comp' := λ _ _ _ f g, by { ext, simp } }

instance linear_yoneda_obj_additive (X : C) : ((linear_yoneda R C).obj X).additive := {}
instance linear_coyoneda_obj_additive (Y : Cᵒᵖ) : ((linear_coyoneda R C).obj Y).additive := {}

@[simp] lemma whiskering_linear_yoneda : linear_yoneda R C ⋙
  (whiskering_right _ _ _).obj (forget (Module.{v} R)) = yoneda :=
rfl

@[simp] lemma whiskering_linear_yoneda₂ : linear_yoneda R C ⋙
  (whiskering_right _ _ _).obj (forget₂ (Module.{v} R) AddCommGroup.{v}) = preadditive_yoneda :=
rfl

@[simp] lemma whiskering_linear_coyoneda : linear_coyoneda R C ⋙
  (whiskering_right _ _ _).obj (forget (Module.{v} R)) = coyoneda :=
rfl

@[simp] lemma whiskering_linear_coyoneda₂ : linear_coyoneda R C ⋙
  (whiskering_right _ _ _).obj (forget₂ (Module.{v} R) AddCommGroup.{v}) = preadditive_coyoneda :=
rfl

instance linear_yoneda_full : full (linear_yoneda R C) :=
let yoneda_full : full (linear_yoneda R C ⋙
  (whiskering_right _ _ _).obj (forget (Module.{v} R))) := yoneda.yoneda_full in
by exactI full.of_comp_faithful (linear_yoneda R C)
  (((whiskering_right _ _ _)).obj (forget (Module.{v} R)))

instance linear_coyoneda_full : full (linear_coyoneda R C) :=
let coyoneda_full : full (linear_coyoneda R C ⋙
  (whiskering_right _ _ _).obj (forget (Module.{v} R))) := coyoneda.coyoneda_full in
by exactI full.of_comp_faithful (linear_coyoneda R C)
  (((whiskering_right _ _ _)).obj (forget (Module.{v} R)))

instance linear_yoneda_faithful : faithful (linear_yoneda R C) :=
faithful.of_comp_eq (whiskering_linear_yoneda R C)

instance linear_coyoneda_faithful : faithful (linear_coyoneda R C) :=
faithful.of_comp_eq (whiskering_linear_coyoneda R C)

end category_theory
