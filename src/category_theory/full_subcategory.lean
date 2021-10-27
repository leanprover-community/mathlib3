/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import category_theory.fully_faithful

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D `from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $$ Hom_C(X, Y) = Hom_D(FX, FY) $$. We call this the
category induced from `D` along `F`.

As a special case, if `C` is a subtype of `D`,
this produces the full subcategory of `D` on the objects belonging to `C`.
In general the induced category is equivalent to the full subcategory of `D` on the
image of `F`.

## Implementation notes

It looks odd to make `D` an explicit argument of `induced_category`,
when it is determined by the argument `F` anyways. The reason to make `D`
explicit is in order to control its syntactic form, so that instances
like `induced_category.has_forget₂` (elsewhere) refer to the correct
form of D. This is used to set up several algebraic categories like

  def CommMon : Type (u+1) := induced_category Mon (bundled.map @comm_monoid.to_monoid)
  -- not `induced_category (bundled monoid) (bundled.map @comm_monoid.to_monoid)`,
  -- even though `Mon = bundled monoid`!
-/

namespace category_theory

universes v u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].

section induced

variables {C : Type u₁} (D : Type u₂) [category.{v} D]
variables (F : C → D)
include F

/--
`induced_category D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint has_inhabited_instance unused_arguments]
def induced_category : Type u₁ := C

variables {D}

instance induced_category.has_coe_to_sort {α : Sort*} [has_coe_to_sort D α] :
  has_coe_to_sort (induced_category D F) α :=
⟨λ c, ↥(F c)⟩

instance induced_category.category : category.{v} (induced_category D F) :=
{ hom  := λ X Y, F X ⟶ F Y,
  id   := λ X, 𝟙 (F X),
  comp := λ _ _ _ f g, f ≫ g }

/--
The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps] def induced_functor : induced_category D F ⥤ D :=
{ obj := F, map := λ x y f, f }

instance induced_category.full : full (induced_functor F) :=
{ preimage := λ x y f, f }
instance induced_category.faithful : faithful (induced_functor F) := {}

end induced

section full_subcategory
/- A full subcategory is the special case of an induced category with F = subtype.val. -/

variables {C : Type u₂} [category.{v} C]
variables (Z : C → Prop)

/--
The category structure on a subtype; morphisms just ignore the property.

See https://stacks.math.columbia.edu/tag/001D. We do not define 'strictly full' subcategories.
-/
instance full_subcategory : category.{v} {X : C // Z X} :=
induced_category.category subtype.val

/--
The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def full_subcategory_inclusion : {X : C // Z X} ⥤ C :=
induced_functor subtype.val

@[simp] lemma full_subcategory_inclusion.obj {X} :
  (full_subcategory_inclusion Z).obj X = X.val := rfl
@[simp] lemma full_subcategory_inclusion.map {X Y} {f : X ⟶ Y} :
  (full_subcategory_inclusion Z).map f = f := rfl

instance full_subcategory.full : full (full_subcategory_inclusion Z) :=
induced_category.full subtype.val
instance full_subcategory.faithful : faithful (full_subcategory_inclusion Z) :=
induced_category.faithful subtype.val

end full_subcategory

end category_theory
