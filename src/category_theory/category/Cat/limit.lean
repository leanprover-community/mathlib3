/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.category.Cat
import category_theory.limits.types
import category_theory.limits.preserves.basic

/-!
# The category of small categories has all small limits.

An object in the limit consists of a family of objects,
which are carried to one another by the functors in the diagram.
A morphism between two such objects is a family of morphisms between the corresponding objects,
which are carried to one another by the action on morphisms of the functors in the diagram.

## Future work
Can the indexing category live in a lower universe?
-/

noncomputable theory

universes v u

open category_theory.limits

namespace category_theory

variables {J : Type v} [small_category J]

namespace Cat

namespace has_limits

instance category_objects {F : J ⥤ Cat.{u u}} {j} :
  small_category ((F ⋙ Cat.objects.{u u}).obj j) :=
(F.obj j).str

/-- Auxiliary definition:
the diagram whose limit gives the morphism space between two objects of the limit category. -/
@[simps]
def hom_diagram {F : J ⥤ Cat.{v v}} (X Y : limit (F ⋙ Cat.objects.{v v})) : J ⥤ Type v :=
{ obj := λ j, limit.π (F ⋙ Cat.objects) j X ⟶ limit.π (F ⋙ Cat.objects) j Y,
  map := λ j j' f g,
  begin
    refine eq_to_hom _ ≫ (F.map f).map g ≫ eq_to_hom _,
    exact (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm,
    exact (congr_fun (limit.w (F ⋙ Cat.objects) f) Y),
  end,
  map_id' := λ X, begin
    ext f, dsimp,
    simp [functor.congr_hom (F.map_id X) f],
  end,
  map_comp' := λ X Y Z f g, begin
    ext h, dsimp,
    simp [functor.congr_hom (F.map_comp f g) h],
    refl,
  end, }

@[simps]
instance (F : J ⥤ Cat.{v v}) : category (limit (F ⋙ Cat.objects)) :=
{ hom := λ X Y, limit (hom_diagram X Y),
  id := λ X, types.limit.mk.{v v} (hom_diagram X X) (λ j, 𝟙 _) (λ j j' f, by simp),
  comp := λ X Y Z f g, types.limit.mk.{v v} (hom_diagram X Z)
    (λ j, limit.π (hom_diagram X Y) j f ≫ limit.π (hom_diagram Y Z) j g)
    (λ j j' h, begin
      rw [←congr_fun (limit.w (hom_diagram X Y) h) f, ←congr_fun (limit.w (hom_diagram Y Z) h) g],
      dsimp,
      simp,
    end), }

/-- Auxiliary definition: the limit category. -/
@[simps]
def limit_cone_X (F : J ⥤ Cat.{v v}) : Cat.{v v} :=
{ α := limit (F ⋙ Cat.objects), }.

/-- Auxiliary definition: the cone over the limit category. -/
@[simps]
def limit_cone (F : J ⥤ Cat.{v v}) : cone F :=
{ X := limit_cone_X F,
  π :=
  { app := λ j,
    { obj := limit.π (F ⋙ Cat.objects) j,
      map := λ X Y, limit.π (hom_diagram X Y) j, },
    naturality' := λ j j' f, category_theory.functor.ext
      (λ X, (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm)
      (λ X Y h, (congr_fun (limit.w (hom_diagram X Y) f) h).symm), } }

/-- Auxiliary definition: the universal morphism to the proposed limit cone. -/
@[simps]
def limit_cone_lift (F : J ⥤ Cat.{v v}) (s : cone F) : s.X ⟶ limit_cone_X F :=
{ obj := limit.lift (F ⋙ Cat.objects)
  { X := s.X,
    π :=
    { app := λ j, (s.π.app j).obj,
      naturality' := λ j j' f, (congr_arg functor.obj (s.π.naturality f) : _), } },
  map := λ X Y f,
  begin
    fapply types.limit.mk.{v v},
    { intro j,
      refine eq_to_hom _ ≫ (s.π.app j).map f ≫ eq_to_hom _;
      simp, },
    { intros j j' h,
      dsimp,
      simp only [category.assoc, functor.map_comp,
        eq_to_hom_map, eq_to_hom_trans, eq_to_hom_trans_assoc],
      rw [←functor.comp_map],
      have := (s.π.naturality h).symm,
      conv at this { congr, skip, dsimp, simp, },
      erw [functor.congr_hom this f],
      dsimp, simp, },
  end, }

@[simp]
lemma limit_π_hom_diagram_eq_to_hom {F : J ⥤ Cat.{v v}}
  (X Y : limit (F ⋙ Cat.objects.{v v})) (j : J) (h : X = Y) :
  limit.π (hom_diagram X Y) j (eq_to_hom h) =
    eq_to_hom (congr_arg (limit.π (F ⋙ Cat.objects.{v v}) j) h) :=
by { subst h, simp, }

/-- Auxiliary definition: the proposed cone is a limit cone. -/
def limit_cone_is_limit (F : J ⥤ Cat.{v v}) : is_limit (limit_cone F) :=
{ lift := limit_cone_lift F,
  fac' := λ s j, category_theory.functor.ext (by tidy) (λ X Y f, types.limit.π_mk _ _ _ _),
  uniq' := λ s m w,
  begin
    symmetry,
    fapply category_theory.functor.ext,
    { intro X,
      ext,
      dsimp, simp only [types.limit.lift_π_apply', ←w j],
      refl, },
    { intros X Y f,
      dsimp, simp [(λ j, functor.congr_hom (w j).symm f)],
      congr, },
  end, }

end has_limits

/-- The category of small categories has all small limits. -/
instance : has_limits (Cat.{v v}) :=
{ has_limits_of_shape := λ J _, by exactI
  { has_limit := λ F, ⟨⟨⟨has_limits.limit_cone F, has_limits.limit_cone_is_limit F⟩⟩⟩, } }

instance : preserves_limits Cat.objects.{v v} :=
{ preserves_limits_of_shape := λ J _, by exactI
  { preserves_limit := λ F,
    preserves_limit_of_preserves_limit_cone (has_limits.limit_cone_is_limit F)
      (limits.is_limit.of_iso_limit (limit.is_limit (F ⋙ Cat.objects))
        (cones.ext (by refl) (by tidy))), }}

end Cat

end category_theory
