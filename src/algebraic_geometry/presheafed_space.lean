-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import algebraic_geometry.presheaf

universes v u

open category_theory
open category_theory.instances
open topological_space

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

namespace algebraic_geometry

structure PresheafedSpace :=
(X : Top.{v})
(𝒪 : presheaf_on_space C X)

instance : has_coe_to_sort (PresheafedSpace.{v} C) :=
{ S := Type v, coe := λ F, F.X.α }

variables {C}

namespace PresheafedSpace

instance underlying_space (F : PresheafedSpace.{v} C) : topological_space F := F.X.str

structure hom (F G : PresheafedSpace.{v} C) :=
(f : F.X ⟶ G.X)
(c : G.𝒪 ⟶ F.𝒪.pushforward f)

@[extensionality] lemma ext {F G : PresheafedSpace.{v} C} (α β : hom F G)
  (w : α.f = β.f) (h : α.c ≫ (whisker_right (nat_trans.op (opens.map_iso _ _ w).inv) F.𝒪) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp at w,
  dsimp [presheaf_on_space.pushforward] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end
.

def id (F : PresheafedSpace.{v} C) : hom F F :=
{ f := 𝟙 F.X,
  c := ((functor.id_comp _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _) }

def comp (F G H : PresheafedSpace.{v} C) (α : hom F G) (β : hom G H) : hom F H :=
{ f := α.f ≫ β.f,
  c := β.c ≫ (whisker_left (opens.map β.f).op α.c) }

variables (C)

section
local attribute [simp] id comp presheaf_on_space.pushforward

instance category_of_PresheafedSpaces : category (PresheafedSpace.{v} C) :=
{ hom  := hom,
  id   := id,
  comp := comp,
  -- I'm still grumpy about these proofs.
  -- When I turned the category of open sets upside down by hand,
  -- I could just leave these out.
  comp_id' := λ X Y f,
  begin
    ext,
    { dsimp [opposite] at X_1,
      cases X_1,
      dsimp,
      erw category_theory.functor.map_id,
      erw category_theory.functor.map_id,
      simp,
      refl },
    { simp }
  end,
  id_comp' := λ X Y f,
  begin
    ext,
    { dsimp [opposite] at X_1,
      cases X_1,
      dsimp,
      erw category_theory.functor.map_id,
      erw category.comp_id,
      simp, },
    { simp }
  end,
  assoc' := λ W X Y Z f g h,
  begin
    tidy,
    erw category_theory.functor.map_id,
    simp,
    refl,
  end }
end
.

variables {C}

@[simp] lemma id_f (F : PresheafedSpace.{v} C) : ((𝟙 F) : F ⟶ F).f = 𝟙 F.X := rfl
@[simp] lemma comp_f {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) :
  (α ≫ β).f = α.f ≫ β.f :=
rfl

-- We don't mark these as simp lemmas, because the innards are pretty unsightly.
lemma id_c (F : PresheafedSpace.{v} C) :
  ((𝟙 F) : F ⟶ F).c = (((functor.id_comp _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _)) :=
rfl
lemma comp_c {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) :
  (α ≫ β).c = (β.c ≫ (whisker_left (opens.map β.f).op α.c)) :=
rfl
end PresheafedSpace

end algebraic_geometry

open algebraic_geometry
variables {C}

namespace category_theory

variables {D : Type u} [𝒟 : category.{v+1} D]
include 𝒟

local attribute [simp] PresheafedSpace.id_c PresheafedSpace.comp_c presheaf_on_space.pushforward

namespace functor

def map_presheaf (F : C ⥤ D) : PresheafedSpace.{v} C ⥤ PresheafedSpace.{v} D :=
{ obj := λ X, { X := X.X, 𝒪 := X.𝒪 ⋙ F },
  map := λ X Y f, { f := f.f, c := whisker_right f.c F } }.

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).X = X.X :=
rfl
@[simp] lemma map_presheaf_obj_𝒪 (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).𝒪 = X.𝒪 ⋙ F :=
rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).f = f.f :=
rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F :=
rfl

end functor

namespace nat_trans

def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
{ app := λ X,
  { f := 𝟙 _,
    c := whisker_left X.𝒪 α ≫ ((functor.id_comp _).inv) ≫ (whisker_right (nat_trans.op (opens.map_id _).hom) _) },
  naturality' := λ X Y f,
  begin
    ext U,
    { dsimp [opposite] at U,
      cases U, -- it would be nice to do without this
      dsimp,
      simp,
      erw category_theory.functor.map_id,
      erw category_theory.functor.map_id,
      erw category_theory.functor.map_id,
      erw category_theory.functor.map_id,
      erw category.comp_id,
      erw category.comp_id,
      simp,
      exact (α.naturality _).symm, },
    { refl, }
  end }.

end nat_trans

end category_theory
