/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.concrete_category.bundled
import category_theory.discrete_category
import category_theory.types
import category_theory.bicategory.strict

/-!
# Category of categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/

universes v u

namespace category_theory

/-- Category of categories. -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
def Cat := bundled category.{v u}

namespace Cat

instance : inhabited Cat := ⟨⟨Type u, category_theory.types⟩⟩

instance : has_coe_to_sort Cat (Type u) := ⟨bundled.α⟩

instance str (C : Cat.{v u}) : category.{v u} C := C.str

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [category.{v} C] : Cat.{v u} := bundled.of C

/-- Bicategory structure on `Cat` -/
instance bicategory : bicategory.{(max v u) (max v u)} Cat.{v u} :=
{ hom := λ C D, C ⥤ D,
  id := λ C, 𝟭 C,
  comp := λ C D E F G, F ⋙ G,
  hom_category := λ C D, functor.category C D,
  whisker_left := λ C D E F G H η, whisker_left F η,
  whisker_right := λ C D E F G η H, whisker_right η H,
  associator := λ A B C D, functor.associator,
  left_unitor :=  λ A B, functor.left_unitor,
  right_unitor := λ A B, functor.right_unitor,
  pentagon' := λ A B C D E, functor.pentagon,
  triangle' := λ A B C, functor.triangle }

/-- `Cat` is a strict bicategory. -/
instance bicategory.strict : bicategory.strict Cat.{v u} :=
{ id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }

/-- Category structure on `Cat` -/
instance category : large_category.{max v u} Cat.{v u} := strict_bicategory.category Cat.{v u}

@[simp]
lemma id_map {C : Cat} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⥤ C).map f = f :=
functor.id_map f

@[simp]
lemma comp_obj {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
  (F ≫ G).obj X = G.obj (F.obj X) :=
functor.comp_obj F G X

@[simp]
lemma comp_map {C D E : Cat} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
  (F ≫ G).map f = G.map (F.map f) :=
functor.comp_map F G f

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v u} ⥤ Type u :=
{ obj := λ C, C,
  map := λ C D F, F.obj }

section
local attribute [simp] eq_to_hom_map

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equiv_of_iso {C D : Cat} (γ : C ≅ D) : C ≌ D :=
{ functor := γ.hom,
  inverse := γ.inv,
  unit_iso := eq_to_iso $ eq.symm γ.hom_inv_id,
  counit_iso := eq_to_iso γ.inv_hom_id }

end

end Cat

/--
Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def Type_to_Cat : Type u ⥤ Cat :=
{ obj := λ X, Cat.of (discrete X),
  map := λ X Y f, discrete.functor (discrete.mk ∘ f),
  map_id' := λ X, begin apply functor.ext, tidy, end,
  map_comp' := λ X Y Z f g, begin apply functor.ext, tidy, end }

instance : faithful Type_to_Cat.{u} :=
{ map_injective' := λ X Y f g h, funext (λ x, congr_arg discrete.as (functor.congr_obj h ⟨x⟩)), }

instance : full Type_to_Cat.{u} :=
{ preimage := λ X Y F, discrete.as ∘ F.obj ∘ discrete.mk,
  witness' :=
  begin
    intros X Y F,
    apply functor.ext,
    { intros x y f, dsimp, ext, },
    { rintros ⟨x⟩, ext, refl, }
  end }

end category_theory
