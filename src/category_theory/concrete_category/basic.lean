/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import category_theory.types category_theory.full_subcategory

/-!
# Concrete categories

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Type*`.  We define concrete categories using `class
concrete_category`.  In particular, we impose no restrictions on the
carrier type `C`, so `Type` is a concrete category with the identity
forgetful functor.

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Type*`.  We say that a concrete category `C` admits a
*forgetful functor* to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget
C`, see `class has_forget₂`.  Due to `faithful.div_comp`, it suffices
to verify that `forget₂.obj` and `forget₂.map` agree with the equality
above; then `forget₂` will satisfy the functor laws automatically, see
`has_forget₂.mk'`.

Two classes helping construct concrete categories in the two most
common cases are provided in the files `bundled_hom` and
`unbundled_hom`, see their documentation for details.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

universe u

namespace category_theory

/-- A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`. -/
class concrete_category (C : Type (u+1)) extends category.{u} C :=
(forget : C ⥤ Type u)
[forget_faithful : faithful forget]

instance (C : Type (u+1)) [concrete_category C] : has_coe_to_sort C :=
{ S := Type u, coe := (concrete_category.forget C).obj }

/-- The forgetful functor from a concrete category to `Type u`. -/
@[reducible] def forget (C : Type (u+1)) [concrete_category C] : C ⥤ Type u :=
concrete_category.forget C

attribute [instance] concrete_category.forget_faithful

instance concrete_category.types : concrete_category (Type u) :=
{ forget := 𝟭 _ }

/--
`has_forget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ C` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class has_forget₂ (C D : Type (u+1)) [concrete_category C] [concrete_category D] :=
(forget₂ : C ⥤ D)
(forget_comp : forget₂ ⋙ (forget D) = forget C)

/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`has_forget C `. -/
@[reducible] def forget₂ (C D : Type (u+1)) [concrete_category C] [concrete_category D]
  [has_forget₂ C D] : C ⥤ D :=
has_forget₂.forget₂ C D

instance forget_faithful (C D : Type (u+1)) [concrete_category C] [concrete_category D]
  [has_forget₂ C D] : faithful (forget₂ C D) :=
(has_forget₂.forget_comp C D).faithful_of_comp

instance induced_category.concrete_category {C D : Type (u+1)} [concrete_category D] (f : C → D) :
  concrete_category (induced_category f) :=
{ forget := induced_functor f ⋙ forget D }

instance induced_category.has_forget₂ {C D : Type (u+1)} [concrete_category D] (f : C → D) :
  has_forget₂ (induced_category f) D :=
{ forget₂ := induced_functor f,
  forget_comp := rfl }

/--
In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def has_forget₂.mk' {C D : Type (u+1)} [concrete_category C] [concrete_category D]
  (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
  (map : Π {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, (forget D).map (map f) == (forget C).map f) :
has_forget₂ C D :=
{ forget₂ := faithful.div _ _ _ @h_obj _ @h_map,
  forget_comp := by apply faithful.div_comp }

instance has_forget_to_Type (C : Type (u+1)) [concrete_category C] : has_forget₂ C (Type u) :=
{ forget₂ := forget C,
  forget_comp := functor.comp_id _ }

end category_theory
