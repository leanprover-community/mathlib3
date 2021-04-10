/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.concrete_category
import category_theory.discrete_category
import category_theory.eq_to_hom

import category_theory.path_category
import category_theory.category.Cat

/-!
# The category of quivers

-/

universes v u

namespace category_theory

/-- Category of quivers. -/
def Quiver := bundled quiver.{v u}

namespace Quiver

instance : has_coe_to_sort Quiver :=
{ S := Type u,
  coe := bundled.α }

instance str (C : Quiver.{v u}) : quiver.{v u} C := C.str

/-- Construct a bundled `Quiver` from the underlying type and the typeclass. -/
def of (C : Type u) [quiver.{v} C] : Quiver.{v u} := bundled.of C

instance : inhabited Quiver := ⟨Quiver.of (quiver.empty pempty)⟩

/-- Category structure on `Quiver` -/
instance category : large_category.{max v u} Quiver.{v u} :=
{ hom := λ C D, prefunctor C D,
  id := λ C, prefunctor.id C,
  comp := λ C D E F G, prefunctor.comp F G,
  id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v u} ⥤ Quiver.{v u} :=
{ obj := λ C, Quiver.of C,
  map := λ C D F,
  { obj := λ X, F.obj X,
    map := λ X Y f, F.map f, }, }

end Quiver

namespace Cat

local attribute [ext] functor.ext

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiver.{v u} ⥤ Cat.{(max u v) u} :=
{ obj := λ V, Cat.of (paths V),
  map := λ V W F,
  { obj := λ X, F.obj X,
    map := λ X Y f, F.map_path f,
    map_comp' := λ X Y Z f g, F.map_path_comp f g, },
  map_id' := λ V, begin
    ext; dsimp,
    { induction f with b c p e ih,
      { refl, },
      { dsimp,
        erw [ih, functor.id_map, functor.id_map, prefunctor.id_map],
        simp, }, },
    { intros X, erw [functor.id_obj, prefunctor.id_obj], refl, },
  end,
  map_comp' := λ U V W F G,
  begin
    ext; dsimp,
    { induction f with b c p e ih,
      { refl, },
      { dsimp,
        erw [ih, functor.id_map, functor.id_map, prefunctor.id_map],
        simp, }, },
    { intros X, erw [functor.id_obj, prefunctor.id_obj], refl, },
  end }

end Cat



end category_theory
