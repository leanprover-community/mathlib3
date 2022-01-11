import category_theory.bicategory.functor
import category_theory.discrete_category

/-!
# Locally discrete bicategories

We give a bicategory structure on a category called the locally discrete bicategory.
The objects and 1-morphisms in the locally discrete bicategory are those in the underlying
category, and the 2-morphisms are the equalities between 1-morphisms.

-/

namespace category_theory

open bicategory category_theory (discrete_category) category functor
open_locale bicategory

universes v u

variables (C : Type u)

namespace bicategory

/-- A type alias for C. -/
def locally_discrete := C

instance [inhabited C] : inhabited (locally_discrete C) := by assumption

instance [category_struct.{v} C] : category_struct (locally_discrete C) := by assumption

variables {C} [category_struct.{v} C]

instance (X Y : locally_discrete C) : small_category (X ⟶ Y) := discrete_category (X ⟶ Y)

/-- Extract the equation from a 2-morphism in a locally discrete bicategory. -/
lemma eq_of_hom {X Y : locally_discrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
η.down.down

end bicategory

open bicategory

variables (C) [category.{v} C]

/--
The locally discrete bicategory associated with a category is a bicategory whose 2-morphisms
are equalities.
-/
instance locally_discrete_bicategory : bicategory.{v v} (locally_discrete C) :=
{ whisker_left  := λ X Y Z f g h η, eq_to_hom (congr_arg2 (≫) rfl (eq_of_hom η)),
  whisker_right := λ X Y Z f g η h, eq_to_hom (congr_arg2 (≫) (eq_of_hom η) rfl),
  associator := λ W X Y Z f g h, eq_to_iso (category.assoc f g h),
  left_unitor  := λ X Y f, eq_to_iso (category.id_comp f),
  right_unitor := λ X Y f, eq_to_iso (category.comp_id f) }

/--
The locally discrete bicategory is strict.
-/
instance locally_discrete_bicategory.strict : strict (locally_discrete C) := { }

universes w₂ v₁ v₂ u₁ u₂

/--
If `B` is a strict bicategory, any functor `I → B` gives an oplax functor
from `locally_discrete I` to `B`.
-/
@[simps]
def functor.to_oplax_functor
  {I : Type u₁} [category.{v₁} I] {B : Type u₂} [bicategory.{w₂ v₂} B] [strict B] (F : I ⥤ B) :
  oplax_functor (locally_discrete I) B :=
{ map₂ := λ X Y f g η, eq_to_hom (congr_arg _ (eq_of_hom η)),
  map_id := λ X, eq_to_hom (F.map_id X),
  map_comp := λ X Y Z f g, eq_to_hom (F.map_comp f g),
  .. F }

end category_theory
