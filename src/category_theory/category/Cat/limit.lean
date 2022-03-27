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


variables {J : Type v} [small_category J]

set_option pp.universes true

instance category_objects {F : J ⥤ Cat.{v v}} {j} :
  small_category ((F ⋙ Cat.objects.{v v}).obj j) :=
(F.obj j).str

instance category_objects' {F : J ⥤ Cat.{v v}} {j} :
  small_category ((Cat.objects.{v v}).obj (F.obj j)) :=
(F.obj j).str

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
def limit (F : J ⥤ Cat.{v v}) : Cat.{v v} :=
{ α := limit (F ⋙ Cat.objects),
  str :=
  { hom := λ X Y, limit (hom_diagram X Y),
    id := λ X, begin fapply types.limit.mk, intro j, dsimp, exact 𝟙 _, intros j j' f, simp, end,
    comp := λ X Y Z f g,
    begin
      fapply types.limit.mk,
      { exact λ j, limit.π (hom_diagram X Y) j f ≫ limit.π (hom_diagram Y Z) j g, },
      { intros j j' h,
        dsimp,
        conv_rhs { rw ←congr_fun (limit.w (hom_diagram X Y) h) f, },
        conv_rhs { rw ←congr_fun (limit.w (hom_diagram Y Z) h) g, },
        dsimp,
        simp, },
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
      naturality' := λ j j' f, (congr_arg functor.obj (s.π.naturality f) : _), } },
  map := λ X Y f,
  begin
    fapply types.limit.mk,
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
lemma limit_π_hom_diagram_eq_to_hom {F : J ⥤ Cat.{v v}}
  (X Y : limit (F ⋙ Cat.objects.{v v})) (j : J) (h : X = Y) :
  limit.π (hom_diagram X Y) j (eq_to_hom h) =
    eq_to_hom (congr_arg (limit.π (F ⋙ Cat.objects.{v v}) j) h) :=
by { subst h, simp, }

/-- The proposed cone is a limit cone. -/
def limit_cone_is_limit (F : J ⥤ Cat.{v v}) : is_limit (limit_cone F) :=
{ lift := limit_cone_lift F,
  fac' := λ s j, category_theory.functor.ext (by tidy) (λ X Y f, types.limit.π_mk _ _ _ _),
  uniq' := λ s m w,
  begin
    symmetry,
    fapply category_theory.functor.ext,
    { intro X,
      ext,
      dsimp, simp only [types.limit.lift_π_apply, ←w j],
      refl, },
    { intros X Y f,
      dsimp, simp [(λ j, functor.congr_hom (w j).symm f)],
      congr, },
  end, }
