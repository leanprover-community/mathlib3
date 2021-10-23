/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.shift
import category_theory.concrete_category

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, zero morphisms and zero objects, and the shift functor
on differential objects.
-/

open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

variables [has_zero_morphisms C] [has_shift C]

/--
A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.
-/
@[nolint has_inhabited_instance]
structure differential_object :=
(X : C)
(d : X ⟶ X⟦1⟧)
(d_squared' : d ≫ d⟦1⟧' = 0 . obviously)

restate_axiom differential_object.d_squared'
attribute [simp] differential_object.d_squared

variables {C}

namespace differential_object

/--
A morphism of differential objects is a morphism commuting with the differentials.
-/
@[ext, nolint has_inhabited_instance]
structure hom (X Y : differential_object C) :=
(f : X.X ⟶ Y.X)
(comm' : X.d ≫ f⟦1⟧' = f ≫ Y.d . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

namespace hom

/-- The identity morphism of a differential object. -/
@[simps]
def id (X : differential_object C) : hom X X :=
{ f := 𝟙 X.X }

/-- The composition of morphisms of differential objects. -/
@[simps]
def comp {X Y Z : differential_object C} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ f := f.f ≫ g.f, }

end hom

instance category_of_differential_objects : category (differential_object C) :=
{ hom := hom,
  id := hom.id,
  comp := λ X Y Z f g, hom.comp f g, }

@[simp]
lemma id_f (X : differential_object C) : ((𝟙 X) : X ⟶ X).f = 𝟙 (X.X) := rfl

@[simp]
lemma comp_f {X Y Z : differential_object C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).f = f.f ≫ g.f :=
rfl

variables (C)

/-- The forgetful functor taking a differential object to its underlying object. -/
def forget : (differential_object C) ⥤ C :=
{ obj := λ X, X.X,
  map := λ X Y f, f.f, }

instance forget_faithful : faithful (forget C) :=
{ }

instance has_zero_morphisms : has_zero_morphisms (differential_object C) :=
{ has_zero := λ X Y,
  ⟨{ f := 0, }⟩}

variables {C}

@[simp]
lemma zero_f (P Q : differential_object C) : (0 : P ⟶ Q).f = 0 := rfl

/--
An isomorphism of differential objects gives an isomorphism of the underlying objects.
-/
@[simps] def iso_app {X Y : differential_object C} (f : X ≅ Y) : X.X ≅ Y.X :=
⟨f.hom.f, f.inv.f, by { dsimp, rw [← comp_f, iso.hom_inv_id, id_f] },
  by { dsimp, rw [← comp_f, iso.inv_hom_id, id_f] }⟩

@[simp] lemma iso_app_refl (X : differential_object C) : iso_app (iso.refl X) = iso.refl X.X := rfl
@[simp] lemma iso_app_symm {X Y : differential_object C} (f : X ≅ Y) :
  iso_app f.symm = (iso_app f).symm := rfl
@[simp] lemma iso_app_trans {X Y Z : differential_object C} (f : X ≅ Y) (g : Y ≅ Z) :
  iso_app (f ≪≫ g) = iso_app f ≪≫ iso_app g := rfl

end differential_object

namespace functor

universes v' u'
variables (D : Type u') [category.{v'} D]
variables [has_zero_morphisms D] [has_shift D]

/--
A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero morphisms
can be lifted to a functor `differential_object C ⥤ differential_object D`.
-/
@[simps]
def map_differential_object (F : C ⥤ D) (η : (shift C).functor.comp F ⟶ F.comp (shift D).functor)
  (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) :
  differential_object C ⥤ differential_object D :=
{ obj := λ X, { X := F.obj X.X,
    d := F.map X.d ≫ η.app X.X,
    d_squared' := begin
      dsimp, rw [functor.map_comp, ← functor.comp_map F (shift D).functor],
      slice_lhs 2 3 { rw [← η.naturality X.d] },
      rw [functor.comp_map],
      slice_lhs 1 2 { rw [← F.map_comp, X.d_squared, hF] },
      rw [zero_comp, zero_comp],
    end },
  map := λ X Y f, { f := F.map f.f,
    comm' := begin
      dsimp,
      slice_lhs 2 3 { rw [← functor.comp_map F (shift D).functor, ← η.naturality f.f] },
      slice_lhs 1 2 { rw [functor.comp_map, ← F.map_comp, f.comm, F.map_comp] },
      rw [category.assoc]
    end },
  map_id' := by { intros, ext, simp },
  map_comp' := by { intros, ext, simp }, }

end functor

end category_theory

namespace category_theory

namespace differential_object

variables (C : Type u) [category.{v} C]

variables [has_zero_object C] [has_zero_morphisms C] [has_shift C]

open_locale zero_object

instance has_zero_object : has_zero_object (differential_object C) :=
{ zero :=
  { X := (0 : C),
    d := 0, },
  unique_to := λ X, ⟨⟨{ f := 0 }⟩, λ f, (by ext)⟩,
  unique_from := λ X, ⟨⟨{ f := 0 }⟩, λ f, (by ext)⟩, }

end differential_object

namespace differential_object

variables (C : Type (u+1)) [large_category C] [concrete_category C]
  [has_zero_morphisms C] [has_shift C]

instance concrete_category_of_differential_objects :
  concrete_category (differential_object C) :=
{ forget := forget C ⋙ category_theory.forget C }

instance : has_forget₂ (differential_object C) C :=
{ forget₂ := forget C }

end differential_object

/-! The category of differential objects itself has a shift functor. -/
namespace differential_object

variables (C : Type u) [category.{v} C]
variables [has_zero_morphisms C] [has_shift C]

/-- The shift functor on `differential_object C`. -/
@[simps]
def shift_functor : differential_object C ⥤ differential_object C :=
{ obj := λ X,
  { X := X.X⟦1⟧,
    d := X.d⟦1⟧',
    d_squared' := begin
      dsimp,
      rw [←functor.map_comp, X.d_squared, is_equivalence_preserves_zero_morphisms],
    end },
  map := λ X Y f,
  { f := f.f⟦1⟧',
    comm' := begin dsimp, rw [←functor.map_comp, f.comm, ←functor.map_comp], end, }, }

/-- The inverse shift functor on `differential C`, at the level of objects. -/
@[simps]
def shift_inverse_obj : differential_object C → differential_object C :=
λ X,
{ X := X.X⟦-1⟧,
  d := X.d⟦-1⟧' ≫ (shift C).unit_inv.app X.X ≫ (shift C).counit_inv.app X.X,
  d_squared' := begin
    dsimp,
    rw functor.map_comp,
    slice_lhs 3 4 { erw ←(shift C).counit_inv.naturality, },
    slice_lhs 2 3 { erw ←(shift C).unit_inv.naturality, },
    slice_lhs 1 2 { erw [←functor.map_comp, X.d_squared], },
    simp,
  end, }

/-- The inverse shift functor on `differential C`. -/
@[simps]
def shift_inverse : differential_object C ⥤ differential_object C :=
{ obj := shift_inverse_obj C,
  map := λ X Y f,
  { f := f.f⟦-1⟧',
    comm' := begin
      dsimp,
      slice_lhs 3 4 { erw ←(shift C).counit_inv.naturality, },
      slice_lhs 2 3 { erw ←(shift C).unit_inv.naturality, },
      slice_lhs 1 2 { erw [←functor.map_comp, f.comm, functor.map_comp], },
      rw [category.assoc, category.assoc],
    end, }, }.

/-- The unit for the shift functor on `differential_object C`. -/
@[simps]
def shift_unit : 𝟭 (differential_object C) ⟶ shift_functor C ⋙ shift_inverse C :=
{ app := λ X,
  { f := (shift C).unit.app X.X,
    comm' := begin
      dsimp,
      slice_rhs 1 2 { erw ←(shift C).unit.naturality, },
      simp only [category.comp_id, functor.id_map, iso.hom_inv_id_app,
        category.assoc, equivalence.counit_inv_app_functor],
    end, }, }

/-- The inverse of the unit for the shift functor on `differential_object C`. -/
@[simps]
def shift_unit_inv : shift_functor C ⋙ shift_inverse C ⟶ 𝟭 (differential_object C) :=
{ app := λ X,
  { f := (shift C).unit_inv.app X.X,
    comm' := begin
      dsimp,
      slice_rhs 1 2 { erw ←(shift C).unit_inv.naturality, },
      rw [equivalence.counit_inv_app_functor],
      slice_lhs 3 4 { rw ←functor.map_comp, },
      simp only [iso.hom_inv_id_app, functor.comp_map, iso.hom_inv_id_app_assoc,
        nat_iso.cancel_nat_iso_inv_left, equivalence.inv_fun_map, category.assoc],
      dsimp,
      rw category_theory.functor.map_id,
    end, }, }.

/-- The unit isomorphism for the shift functor on `differential_object C`. -/
@[simps]
def shift_unit_iso : 𝟭 (differential_object C) ≅ shift_functor C ⋙ shift_inverse C :=
{ hom := shift_unit C,
  inv := shift_unit_inv C, }.

/-- The counit for the shift functor on `differential_object C`. -/
@[simps]
def shift_counit : shift_inverse C ⋙ shift_functor C ⟶ 𝟭 (differential_object C) :=
{ app := λ X,
  { f := (shift C).counit.app X.X,
    comm' :=
    begin
      dsimp,
      slice_rhs 1 2 { erw ←(shift C).counit.naturality, },
      rw [(shift C).functor.map_comp, (shift C).functor.map_comp],
      slice_lhs 3 4 { erw [←functor.map_comp, iso.inv_hom_id_app, functor.map_id], },
      erw equivalence.counit_app_functor,
      rw category.comp_id,
      refl,
    end, }, }

/-- The inverse of the counit for the shift functor on `differential_object C`. -/
@[simps]
def shift_counit_inv : 𝟭 (differential_object C) ⟶ shift_inverse C ⋙ shift_functor C :=
{ app := λ X,
  { f := (shift C).counit_inv.app X.X,
    comm' :=
    begin
      dsimp,
      rw [(shift C).functor.map_comp, (shift C).functor.map_comp],
      slice_rhs 1 2 { erw ←(shift C).counit_inv.naturality, },
      rw ←equivalence.counit_app_functor,
      slice_rhs 2 3 { rw iso.inv_hom_id_app, },
      rw category.id_comp,
      refl,
    end, }, }

/-- The counit isomorphism for the shift functor on `differential_object C`. -/
@[simps]
def shift_counit_iso : shift_inverse C ⋙ shift_functor C ≅ 𝟭 (differential_object C) :=
{ hom := shift_counit C,
  inv := shift_counit_inv C, }

/--
The category of differential objects in `C` itself has a shift functor.
-/
instance : has_shift (differential_object C) :=
{ shift :=
  { functor := shift_functor C,
    inverse := shift_inverse C,
    unit_iso := shift_unit_iso C,
    counit_iso := shift_counit_iso C, } }

end differential_object

end category_theory
