/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import category_theory.functor.fully_faithful

/-!
# Induced categories and full subcategories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

universes v v₂ u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].

section induced

variables {C : Type u₁} (D : Type u₂) [category.{v} D]
variables (F : C → D)
include F

/--
`induced_category D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint has_nonempty_instance unused_arguments]
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

variables {C : Type u₁} [category.{v} C]
variables (Z : C → Prop)

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories.

See <https://stacks.math.columbia.edu/tag/001D>. We do not define 'strictly full' subcategories.
-/
@[ext, nolint has_nonempty_instance] structure full_subcategory :=
(obj : C)
(property : Z obj)

instance full_subcategory.category : category.{v} (full_subcategory Z) :=
induced_category.category full_subcategory.obj

/--
The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def full_subcategory_inclusion : full_subcategory Z ⥤ C :=
induced_functor full_subcategory.obj

@[simp] lemma full_subcategory_inclusion.obj {X} :
  (full_subcategory_inclusion Z).obj X = X.obj := rfl
@[simp] lemma full_subcategory_inclusion.map {X Y} {f : X ⟶ Y} :
  (full_subcategory_inclusion Z).map f = f := rfl

instance full_subcategory.full : full (full_subcategory_inclusion Z) :=
induced_category.full _
instance full_subcategory.faithful : faithful (full_subcategory_inclusion Z) :=
induced_category.faithful _

variables {Z} {Z' : C → Prop}

/-- An implication of predicates `Z → Z'` induces a functor between full subcategories. -/
@[simps]
def full_subcategory.map (h : ∀ ⦃X⦄, Z X → Z' X) : full_subcategory Z ⥤ full_subcategory Z' :=
{ obj := λ X, ⟨X.1, h X.2⟩,
  map := λ X Y f, f }

instance (h : ∀ ⦃X⦄, Z X → Z' X) : full (full_subcategory.map h) :=
{ preimage := λ X Y f, f }

instance (h : ∀ ⦃X⦄, Z X → Z' X) : faithful (full_subcategory.map h) := {}

@[simp] lemma full_subcategory.map_inclusion (h : ∀ ⦃X⦄, Z X → Z' X) :
  full_subcategory.map h ⋙ full_subcategory_inclusion Z' = full_subcategory_inclusion Z :=
rfl

section lift
variables {D : Type u₂} [category.{v₂} D] (P Q : D → Prop)

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps]
def full_subcategory.lift (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) : C ⥤ full_subcategory P :=
{ obj := λ X, ⟨F.obj X, hF X⟩,
  map := λ X Y f, F.map f }

/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. Unfortunately, this is not true by definition, so we only get a natural
    isomorphism, but it is pointwise definitionally true, see
    `full_subcategory.inclusion_obj_lift_obj` and `full_subcategory.inclusion_map_lift_map`. -/
def full_subcategory.lift_comp_inclusion (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
  full_subcategory.lift P F hF ⋙ full_subcategory_inclusion P ≅ F :=
nat_iso.of_components (λ X, iso.refl _) (by simp)

@[simp]
lemma full_subcategory.inclusion_obj_lift_obj (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X : C} :
  (full_subcategory_inclusion P).obj ((full_subcategory.lift P F hF).obj X) = F.obj X :=
rfl

lemma full_subcategory.inclusion_map_lift_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) {X Y : C}
  (f : X ⟶ Y) :
  (full_subcategory_inclusion P).map ((full_subcategory.lift P F hF).map f) = F.map f :=
rfl

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [faithful F] :
  faithful (full_subcategory.lift P F hF) :=
faithful.of_comp_iso (full_subcategory.lift_comp_inclusion P F hF)

instance (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) [full F] : full (full_subcategory.lift P F hF) :=
full.of_comp_faithful_iso (full_subcategory.lift_comp_inclusion P F hF)

@[simp]
lemma full_subcategory.lift_comp_map (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) (h : ∀ ⦃X⦄, P X → Q X) :
  full_subcategory.lift P F hF ⋙ full_subcategory.map h =
    full_subcategory.lift Q F (λ X, h (hF X)) :=
rfl

end lift

end full_subcategory

end category_theory
