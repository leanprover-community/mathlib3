/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.path_category
import category_theory.category.Cat

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.

-/

universes v u

namespace category_theory

/-- Category of quivers. -/
def Quiv := bundled quiver.{(v+1) u}

namespace Quiv

instance : has_coe_to_sort Quiv :=
{ S := Type u,
  coe := bundled.α }

instance str (C : Quiv.{v u}) : quiver.{(v+1) u} C := C.str

/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
def of (C : Type u) [quiver.{v+1} C] : Quiv.{v u} := bundled.of C

instance : inhabited Quiv := ⟨Quiv.of (quiver.empty pempty)⟩

/-- Category structure on `Quiv` -/
instance category : large_category.{max v u} Quiv.{v u} :=
{ hom := λ C D, prefunctor C D,
  id := λ C, prefunctor.id C,
  comp := λ C D E F G, prefunctor.comp F G,
  id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v u} ⥤ Quiv.{v u} :=
{ obj := λ C, Quiv.of C,
  map := λ C D F, F.to_prefunctor, }

end Quiv

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiv.{v u} ⥤ Cat.{(max u v) u} :=
{ obj := λ V, Cat.of (paths V),
  map := λ V W F,
  { obj := λ X, F.obj X,
    map := λ X Y f, F.map_path f,
    map_comp' := λ X Y Z f g, F.map_path_comp f g, },
  map_id' := λ V, by { change (show paths V ⥤ _, from _) = _, ext, apply eq_conj_eq_to_hom, refl },
  map_comp' := λ U V W F G,
    by { change (show paths U ⥤ _, from _) = _, ext, apply eq_conj_eq_to_hom, refl } }

end Cat

namespace Quiv

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [quiver.{v+1} V] {C : Type u} [category.{v} C]
  (F : prefunctor V C) : paths V ⥤ C :=
{ obj := λ X, F.obj X,
  map := λ X Y f, compose_path (F.map_path f), }

-- We might construct `of_lift_iso_self : paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!

/--
The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
def adj : Cat.free ⊣ Quiv.forget :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ V C,
  { to_fun := λ F, paths.of.comp F.to_prefunctor,
    inv_fun := λ F, lift F,
    left_inv := λ F, by { ext, { erw (eq_conj_eq_to_hom _).symm, apply category.id_comp }, refl },
    right_inv := begin
      rintro ⟨obj,map⟩,
      dsimp only [prefunctor.comp],
      congr,
      ext X Y f,
      exact category.id_comp _,
    end, },
  hom_equiv_naturality_left_symm' := λ V W C f g,
    by { change (show paths V ⥤ _, from _) = _, ext, apply eq_conj_eq_to_hom, refl } }

end Quiv

end category_theory
