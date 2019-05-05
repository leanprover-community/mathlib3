-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.instances.Top.presheaf

universes v u

open category_theory
open category_theory.instances
open category_theory.instances.Top
open topological_space

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

namespace algebraic_geometry

structure PresheafedSpace :=
(to_Top : Top.{v})
(𝒪 : to_Top.presheaf C)

variables {C}

namespace PresheafedSpace

instance : has_coe_to_sort (PresheafedSpace.{v} C) :=
{ S := Type v, coe := λ F, F.to_Top.α }

instance (X : PresheafedSpace.{v} C) : topological_space X := X.to_Top.str

structure hom (X Y : PresheafedSpace.{v} C) :=
(f : X.to_Top ⟶ Y.to_Top)
(c : Y.𝒪 ⟶ f _* X.𝒪)

@[extensionality] lemma ext {X Y : PresheafedSpace.{v} C} (α β : hom X Y)
  (w : α.f = β.f) (h : α.c ≫ (whisker_right (nat_trans.op (opens.map_iso _ _ w).inv) X.𝒪) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp [presheaf.pushforward] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end
.

def id (X : PresheafedSpace.{v} C) : hom X X :=
{ f := 𝟙 X.to_Top,
  c := ((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _) }

def comp (X Y Z : PresheafedSpace.{v} C) (α : hom X Y) (β : hom Y Z) : hom X Z :=
{ f := α.f ≫ β.f,
  c := β.c ≫ (whisker_left (opens.map β.f).op α.c) }

variables (C)

section
local attribute [simp] id comp presheaf.pushforward

instance category_of_PresheafedSpaces : category (PresheafedSpace.{v} C) :=
{ hom  := hom,
  id   := id,
  comp := comp,
  -- I'm still grumpy about these proofs.
  -- The obstacle here is the mysterious need to use `erw` for some `simp` lemmas.
  -- If we could avoid that, locally adding `op_induction` to `tidy` would discharge these.
  comp_id' := λ X Y f,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp, },
    { simp }
  end,
  id_comp' := λ X Y f,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp only [category.assoc],
      -- This should be done by `simp`, but unfortunately isn't.
      erw [category_theory.functor.map_id],
      simp, },
    { simp }
  end,
  assoc' := λ W X Y Z f g h,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp only [category.assoc],
      -- This should be done by `simp`, but unfortunately isn't.
      erw [category_theory.functor.map_id],
      simp, },
    { refl }
  end }
end
.

variables {C}

instance {X Y : PresheafedSpace.{v} C} : has_coe (X ⟶ Y) (X.to_Top ⟶ Y.to_Top) :=
{ coe := λ α, α.f }

@[simp] lemma id_f (X : PresheafedSpace.{v} C) :
  ((𝟙 X) : X ⟶ X).f = 𝟙 X.to_Top :=
rfl
@[simp] lemma id_coe (X : PresheafedSpace.{v} C) :
  (((𝟙 X) : X ⟶ X) : X.to_Top ⟶ X.to_Top) = 𝟙 X.to_Top :=
rfl
@[simp] lemma comp_f {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) :
  (α ≫ β).f = α.f ≫ β.f :=
rfl
@[simp] lemma comp_coe {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) :
  ((α ≫ β : X ⟶ Z) : X.to_Top ⟶ Z.to_Top) = (α : X.to_Top ⟶ Y.to_Top) ≫ (β : Y.to_Top ⟶ Z.to_Top) :=
rfl

-- We don't mark these as simp lemmas, because the innards are pretty unsightly.
lemma id_c (X : PresheafedSpace.{v} C) :
  ((𝟙 X) : X ⟶ X).c =
  (((functor.left_unitor _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _)) :=
rfl
lemma comp_c {X Y Z : PresheafedSpace.{v} C} (α : X ⟶ Y) (β : Y ⟶ Z) :
  (α ≫ β).c = (β.c ≫ (whisker_left (opens.map β.f).op α.c)) :=
rfl

def forget : PresheafedSpace.{v} C ⥤ Top :=
{ obj := λ X, X.to_Top,
  map := λ X Y f, f }

end PresheafedSpace

end algebraic_geometry

open algebraic_geometry
variables {C}

namespace category_theory

variables {D : Type u} [𝒟 : category.{v+1} D]
include 𝒟

local attribute [simp] PresheafedSpace.id_c PresheafedSpace.comp_c presheaf.pushforward

namespace functor

def map_presheaf (F : C ⥤ D) : PresheafedSpace.{v} C ⥤ PresheafedSpace.{v} D :=
{ obj := λ X, { to_Top := X.to_Top, 𝒪 := X.𝒪 ⋙ F },
  map := λ X Y f, { f := f.f, c := whisker_right f.c F } }.

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).to_Top = X.to_Top :=
rfl
@[simp] lemma map_presheaf_obj_𝒪 (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).𝒪 = X.𝒪 ⋙ F :=
rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).f = f :=
rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F :=
rfl

end functor

namespace nat_trans

def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
{ app := λ X,
  { f := 𝟙 _,
    c := whisker_left X.𝒪 α ≫ ((functor.left_unitor _).inv) ≫
           (whisker_right (nat_trans.op (opens.map_id _).hom) _) },
  naturality' := λ X Y f,
  begin
    ext U,
    { op_induction U,
      cases U,
      dsimp,
      simp only [functor.map_id, category.id_comp, category.comp_id, category.assoc],
      -- This should be done by `simp`, but unfortunately isn't.
      erw category_theory.functor.map_id,
      erw category_theory.functor.map_id,
      simp only [category.comp_id],
      exact (α.naturality _).symm, },
    { refl, }
  end }.

end nat_trans

end category_theory
