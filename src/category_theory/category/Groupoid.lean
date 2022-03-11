/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.single_obj
import category_theory.limits.shapes.products
import category_theory.pi.basic
import category_theory.limits.is_limit

/-!
# Category of groupoids

This file contains the definition of the category `Groupoid` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Groupoid ⥤ Type`
and `forget_to_Cat : Groupoid ⥤ Cat`.

## Implementation notes

Though `Groupoid` is not a concrete category, we use `bundled` to define
its carrier type.
-/

universes v u

namespace category_theory

/-- Category of groupoids -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
def Groupoid := bundled groupoid.{v u}

namespace Groupoid

instance : inhabited Groupoid := ⟨bundled.of (single_obj punit)⟩

instance str (C : Groupoid.{v u}) : groupoid.{v u} C.α := C.str

instance : has_coe_to_sort Groupoid Type* := bundled.has_coe_to_sort

/-- Construct a bundled `Groupoid` from the underlying type and the typeclass. -/
def of (C : Type u) [groupoid.{v} C] : Groupoid.{v u} := bundled.of C

@[simp] lemma coe_of (C : Type u) [groupoid C] : (of C : Type u) = C := rfl

/-- Category structure on `Groupoid` -/
instance category : large_category.{max v u} Groupoid.{v u} :=
{ hom := λ C D, C ⥤ D,
  id := λ C, 𝟭 C,
  comp := λ C D E F G, F ⋙ G,
  id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Groupoid.{v u} ⥤ Type u :=
{ obj := bundled.α,
  map := λ C D F, F.obj }

/-- Forgetting functor to `Cat` -/
def forget_to_Cat : Groupoid.{v u} ⥤ Cat.{v u} :=
{ obj := λ C, Cat.of C,
  map := λ C D, id }

instance forget_to_Cat_full : full forget_to_Cat :=
{ preimage := λ C D, id }

instance forget_to_Cat_faithful : faithful forget_to_Cat := { }

/-- Convert arrows in the category of groupoids to functors,
which sometimes helps in applying simp lemmas -/
lemma hom_to_functor {C D E : Groupoid.{v u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g := rfl

section products

/-- The cone for the product of a family of groupoids indexed by J is a limit cone -/
@[simps]
def pi_limit_cone {J : Type u} (F : discrete J ⥤ Groupoid.{u u}) :
  limits.limit_cone F :=
{ cone :=
    { X := @of (Π j : J, F.obj j) _,
      π := { app := λ j : J, category_theory.pi.eval _ j, } },
  is_limit :=
  { lift := λ s, functor.pi' s.π.app,
    fac' := by { intros, simp [hom_to_functor], },
    uniq' :=
    begin
      intros s m w,
      apply functor.pi_ext,
      intro j, specialize w j,
      simpa,
    end } }

/-- `pi_limit_cone` reinterpreted as a fan -/
abbreviation pi_limit_fan {J : Type u} (F : J → Groupoid.{u u}) : limits.fan F :=
(pi_limit_cone (discrete.functor F)).cone

instance has_pi : limits.has_products Groupoid.{u u} :=
λ J, { has_limit := λ F, { exists_limit := nonempty.intro (pi_limit_cone F) } }

/-- The product of a family of groupoids is isomorphic
to the product object in the category of Groupoids -/
noncomputable def pi_iso_pi (J : Type u) (f : J → Groupoid.{u u}) : @of (Π j, f j) _ ≅ ∏ f :=
limits.is_limit.cone_point_unique_up_to_iso
  (pi_limit_cone (discrete.functor f)).is_limit
  (limits.limit.is_limit (discrete.functor f))

@[simp]
lemma pi_iso_pi_hom_π (J : Type u) (f : J → Groupoid.{u u}) (j : J) :
  (pi_iso_pi J f).hom ≫ (limits.pi.π f j) = category_theory.pi.eval _ j :=
by { simp [pi_iso_pi], refl, }

end products

end Groupoid

end category_theory
