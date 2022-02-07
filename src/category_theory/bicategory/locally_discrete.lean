/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.discrete_category
import category_theory.bicategory.functor
import category_theory.bicategory.strict

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `locally_discrete C`. The objects and the
1-morphisms in `locally_discrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `locally_discrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `locally_discrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/

namespace category_theory

open bicategory discrete
open_locale bicategory

universes w₂ v v₁ v₂ u u₁ u₂

variables (C : Type u)

/--
A type alias for promoting any category to a bicategory,
with the only 2-morphisms being equalities.
-/
def locally_discrete := C

namespace locally_discrete

instance : Π [inhabited C], inhabited (locally_discrete C) := id

instance : Π [category_struct.{v} C], category_struct (locally_discrete C) := id

variables {C} [category_struct.{v} C]

instance (X Y : locally_discrete C) : small_category (X ⟶ Y) :=
category_theory.discrete_category (X ⟶ Y)

end locally_discrete

variables (C) [category.{v} C]

/--
The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locally_discrete_bicategory : bicategory (locally_discrete C) :=
{ whisker_left  := λ X Y Z f g h η, eq_to_hom (congr_arg2 (≫) rfl (eq_of_hom η)),
  whisker_right := λ X Y Z f g η h, eq_to_hom (congr_arg2 (≫) (eq_of_hom η) rfl),
  associator := λ W X Y Z f g h, eq_to_iso (category.assoc f g h),
  left_unitor  := λ X Y f, eq_to_iso (category.id_comp f),
  right_unitor := λ X Y f, eq_to_iso (category.comp_id f) }

/-- A locally discrete bicategory is strict. -/
instance locally_discrete_bicategory.strict : strict (locally_discrete C) := { }

variables {I : Type u₁} [category.{v₁} I] {B : Type u₂} [bicategory.{w₂ v₂} B] [strict B]


variables (I B)

structure onecat_to_strict extends prefunctor I B :=
(map_id (X : I) : map (𝟙 X) ⟶ 𝟙 (obj X))
(map_comp ⦃X Y Z : I⦄ (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ⟶ map f ≫ map g)
(id_comp : ∀ ⦃X Y : I⦄ (f : X ⟶ Y), map_comp (𝟙 X) f ≫ (map_id X ▷ map f) =
  eq_to_hom (by simp) . obviously)
(comp_id : ∀ ⦃X Y : I⦄ (f : X ⟶ Y), map_comp f (𝟙 Y) ≫ (map f ◁ map_id Y) =
  eq_to_hom (by simp) . obviously)
(assoc : ∀ ⦃X Y Z W : I⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
  map_comp (f ≫ g) h ≫ (map_comp f g ▷ map h) = eq_to_hom (by simp) ≫
  map_comp f (g ≫ h) ≫ (map f ◁ map_comp g h) ≫ eq_to_hom (by simp) . obviously)

variables {I B} (F : onecat_to_strict I B) (G : oplax_functor (locally_discrete I) B)

@[simps]
def functor.to_onecat_to_strict (F : I ⥤ B) : onecat_to_strict I B :=
{ map_id := λ i, eq_to_hom (F.map_id i),
  map_comp := λ i j k f g, eq_to_hom (F.map_comp f g),
  .. F }

@[simps] def onecat_to_strict.to_oplax_functor : oplax_functor (locally_discrete I) B :=
{ map₂ := λ _ _ _ _ f, eq_to_hom (by rw eq_of_hom f),
  map₂_associator' := λ _ _ _ _ f g h, by { dsimp,
    rw [←category.assoc (F.map_comp _ _), F.assoc], simp },
  map₂_left_unitor' := λ _ _ f, by { rw [←category.assoc, F.id_comp], simp },
  map₂_right_unitor' := λ _ _ f, by { rw [←category.assoc, F.comp_id], simp },
  .. F }

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `locally_discrete I` to `B`.
-/
@[simps]
def functor.to_oplax_functor (F : I ⥤ B) : oplax_functor (locally_discrete I) B :=
F.to_onecat_to_strict.to_oplax_functor

@[simps] def oplax_functor.to_onecat_to_strict : onecat_to_strict I B :=
{ id_comp := λ _ _ f, by { have := eq_whisker ((G.map₂_left_unitor' f).symm.trans
    (eq_to_hom_map (G.map_functor _ _) _)) (λ_ _).inv, simp at this, exact this },
  comp_id := λ _ _ f, by { have := eq_whisker ((G.map₂_right_unitor' f).symm.trans
    (eq_to_hom_map (G.map_functor _ _) _)) (ρ_ _).inv, simp at this, exact this },
  assoc := λ _ _ _ _ f g h, by { have := eq_whisker ((G.map₂_associator' f g h).symm.trans
    (eq_whisker (eq_to_hom_map (G.map_functor _ _) _) _)) (α_ _ _ _).inv, simp at this, exact this },
  .. G }

/-- -/
def onecat_to_strict_equiv_oplax_functor :
  onecat_to_strict I B ≃ oplax_functor (locally_discrete I) B :=
{ to_fun := λ F, F.to_oplax_functor,
  inv_fun := λ G, G.to_onecat_to_strict,
  left_inv := λ F, by { cases F with F, cases F, refl } ,
  right_inv := λ G, by { let := G.map_functor, cases G, dsimp [onecat_to_strict.to_oplax_functor],
    congr, ext _ _ _ _ f, convert (eq_to_hom_map (this _ _) (eq_of_hom f)).symm } }


end category_theory
