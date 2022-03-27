/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.category.Cat
import category_theory.limits.types

/-!
# The category of small categories has all small limits.

An object in the limit consists of a family of objects,
which are carried to one another by the functors in the diagram.
A morphism between two such objects is a family of morphisms between the corresponding objects,
which are carried to one another by the action on morphisms of the functors in the diagram.

## Future work
The universe restrictions are likely unnecessarily strict.
-/

noncomputable theory

universes v u

open category_theory
open category_theory.limits

-- @[simp] lemma foo {C D E : Cat.{v u}} (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = f ⋙ g := rfl
-- @[simp] lemma bar {C D : Cat.{v u}} (f : C ⟶ D) : 𝟙 C ⋙ f = f := sorry

variables {J : Type v} [small_category J]

set_option pp.universes true

instance category_objects {F : J ⥤ Cat.{v v}} {j} :
  small_category ((F ⋙ Cat.objects.{v v}).obj j) :=
(F.obj j).str

instance category_objects' {F : J ⥤ Cat.{v v}} {j} :
  small_category ((Cat.objects.{v v}).obj (F.obj j)) :=
(F.obj j).str

@[simps]
def hom_diagram {F : J ⥤ Cat.{v v}} (X Y : limit (F ⋙ Cat.objects.{v v})) : J ⥤ Type v :=
{ obj := λ j, limit.π (F ⋙ Cat.objects) j X ⟶ limit.π (F ⋙ Cat.objects) j Y,
  map := λ j j' f g,
    eq_to_hom (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm ≫
      (F.map f).map g ≫
      eq_to_hom (congr_fun (limit.w (F ⋙ Cat.objects) f) Y),
  map_id' := λ X, begin
    ext f, dsimp,
    simp [functor.congr_hom (F.map_id X) f, Cat.id_map],
  end,
  map_comp' := λ X Y Z f g, begin
    ext h, dsimp,
    simp [functor.congr_hom (F.map_comp f g) h, Cat.comp_map],
    refl,
  end, }

@[simps]
def limit (F : J ⥤ Cat.{v v}) : Cat.{v v} :=
{ α := limit (F ⋙ Cat.objects),
  str :=
  { hom := λ X Y, limit (hom_diagram X Y),
    id := λ X, begin
      fapply types.limit.mk,
      intro j, exact 𝟙 _,
      intros j j' f, dsimp, simp,
    end,
    comp := λ X Y Z f g,
    begin
      fapply types.limit.mk,
      exact (λ j, limit.π (hom_diagram X Y) j f ≫ limit.π (hom_diagram Y Z) j g),
      intros j j' h,
      conv_rhs { rw ←congr_fun (limit.w (hom_diagram X Y) h) f, },
      conv_rhs { rw ←congr_fun (limit.w (hom_diagram Y Z) h) g, },
      dsimp,
      simp,
    end } }.



@[simps]
def limit_cone (F : J ⥤ Cat.{v v}) : cone F :=
{ X := limit F,
  π :=
  { app := λ j,
    { obj := limit.π (F ⋙ Cat.objects) j,
      map := λ X Y, limit.π (hom_diagram X Y) j,
      map_id' := by tidy,
      map_comp' := by tidy, },
    naturality' := λ j j' f, category_theory.functor.ext
      (λ X, (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm)
      (λ X Y h, (congr_fun (limit.w (hom_diagram X Y) f) h).symm), } }

@[simps]
def limit_cone_lift (F : J ⥤ Cat.{v v}) (s : cone F) : s.X ⟶ limit F :=
{ obj := limit.lift (F ⋙ Cat.objects)
  { X := s.X,
    π :=
    { app := λ j, (s.π.app j).obj,
      naturality' := λ j j' f,
      begin
        ext X,
        exact congr_fun (congr_arg functor.obj (s.π.naturality f) : _) X,
      end, } },
  map := λ X Y f,
  begin
    dsimp, fapply types.limit.mk,
    { intro j,
      dsimp,
      refine eq_to_hom _ ≫ (s.π.app j).map f ≫ eq_to_hom _;
      simp, },
    { intros j j' h,
      dsimp,
      simp only [category.assoc, eq_to_hom_trans_assoc, functor.map_comp,
        eq_to_hom_map, eq_to_hom_trans],
      rw [←functor.comp_map],
      have := (s.π.naturality h).symm,
      conv at this { congr, skip, dsimp, simp, },
      erw [functor.congr_hom this f],
      dsimp, simp, },
  end, }

instance quux (F : J ⥤ Cat.{v v}) : category.{v v} (limit.{v v v v+1} (F ⋙ Cat.objects.{v v})) :=
(limit F).str

@[simp]
lemma fooo {F : J ⥤ Cat.{v v}} (X Y : limit (F ⋙ Cat.objects.{v v})) (j : J) (h : X = Y) :
  limit.π (hom_diagram X Y) j (eq_to_hom h) =
    eq_to_hom (congr_arg (limit.π (F ⋙ Cat.objects.{v v}) j) h) :=
by { subst h, simp, }

def limit_cone_is_limit (F : J ⥤ Cat.{v v}) : is_limit (limit_cone F) :=
{ lift := limit_cone_lift F,
  fac' := λ s j, category_theory.functor.ext (by tidy)
    (by { intros X Y f, convert types.limit.π_mk _ _ _ _, dsimp, simp, }),
  uniq' := λ s m w,
  begin
    symmetry,
    fapply category_theory.functor.ext,
    { dsimp,
      intro X,
      ext,
      simp only [types.limit.lift_π_apply, ←w j],
      refl, },
    { intros X Y f,
      dsimp only [limit_cone_lift],
      simp_rw (λ j, functor.congr_hom (w j).symm f),
      dsimp, simp, congr, },
  end, }
