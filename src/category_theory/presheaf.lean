-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Mario Carneiro, Reid Barton

import category_theory.instances.topological_spaces
import category_theory.whiskering
import category_theory.natural_isomorphism
import topology.basic

open topological_space

universes v u

open category_theory
open category_theory.instances

namespace category_theory

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

def presheaf (X : Top.{v}) := opens X ⥤ C

instance category_presheaf (X : Top.{v}) : category (presheaf C X) :=
by dsimp [presheaf]; apply_instance

namespace presheaf
variables {C}

def pushforward {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : presheaf C X) : presheaf C Y :=
(opens.map f) ⋙ ℱ

def pushforward_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : presheaf C X) :
  ℱ.pushforward f ≅ ℱ.pushforward g :=
ℱ.map_nat_iso (opens.map_iso f g h)
def pushforward_eq_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : presheaf C X) :
  ℱ.pushforward_eq h₁ = ℱ.pushforward_eq h₂ :=
rfl

namespace pushforward
def id {X : Top.{v}} (ℱ : presheaf C X) : ℱ.pushforward (𝟙 X) ≅ ℱ :=
ℱ.map_nat_iso (opens.map_id X) ≪≫ functor.left_unitor _

@[simp] lemma id_hom_app {X : Top.{v}} (ℱ : presheaf C X) (U) : (id ℱ).hom.app U = ℱ.map (𝟙 U) :=
begin
  dsimp [id],
  simp,
end
@[simp] lemma id_inv_app {X : Top.{v}} (ℱ : presheaf C X) (U) : (id ℱ).inv.app U = ℱ.map (𝟙 U) :=
begin
  dsimp [id],
  simp,
end

def comp {X Y Z : Top.{v}}  (ℱ : presheaf C X) (f : X ⟶ Y) (g : Y ⟶ Z) : ℱ.pushforward (f ≫ g) ≅ (ℱ.pushforward f).pushforward g :=
ℱ.map_nat_iso (opens.map_comp f g)

@[simp] lemma comp_hom_app {X Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : presheaf C X) (U) : (comp ℱ f g).hom.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  simp,
end
@[simp] lemma comp_inv_app {X Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : presheaf C X) (U) : (comp ℱ f g).inv.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  simp,
  dsimp,
  simp,
end

end pushforward

end presheaf


structure PresheafedSpace :=
(X : Top.{v})
(𝒪 : presheaf C X)

instance : has_coe_to_sort (PresheafedSpace.{v} C) :=
{ S := Type v, coe := λ F, F.X.α }

variables {C}

namespace PresheafedSpace

instance underlying_space (F : PresheafedSpace.{v} C) : topological_space F := F.X.str

structure hom (F G : PresheafedSpace.{v} C) :=
(f : F.X ⟶ G.X)
(c : G.𝒪 ⟹ F.𝒪.pushforward f)

@[extensionality] lemma ext {F G : PresheafedSpace.{v} C} (α β : hom F G)
  (w : α.f = β.f) (h : α.c ⊟ (whisker_right (opens.map_iso _ _ w).hom F.𝒪) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp at w,
  dsimp [presheaf.pushforward] at *,
  tidy, -- including `injections` would make tidy work earlier.
end
.

def id (F : PresheafedSpace.{v} C) : hom F F :=
{ f := 𝟙 F.X,
  c := ((functor.id_comp _).inv) ⊟ (whisker_right (opens.map_id _).inv _) }

def comp (F G H : PresheafedSpace.{v} C) (α : hom F G) (β : hom G H) : hom F H :=
{ f := α.f ≫ β.f,
  c := β.c ⊟ (whisker_left (opens.map β.f) α.c) }

variables (C)

section
local attribute [simp] id comp presheaf.pushforward

instance category_of_presheaves : category (PresheafedSpace.{v} C) :=
{ hom  := hom,
  id   := id,
  comp := comp, }.
end

variables {C}

@[simp] lemma id_f (F : PresheafedSpace.{v} C) : ((𝟙 F) : F ⟶ F).f = 𝟙 F.X := rfl
@[simp] lemma comp_f {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) :
  (α ≫ β).f = α.f ≫ β.f :=
rfl

-- We don't mark these are simp lemmas, because the innards are pretty unsightly.
lemma id_c (F : PresheafedSpace.{v} C) :
  ((𝟙 F) : F ⟶ F).c = (((functor.id_comp _).inv) ⊟ (whisker_right (opens.map_id _).inv _)) :=
rfl
lemma comp_c {F G H : PresheafedSpace.{v} C} (α : F ⟶ G) (β : G ⟶ H) :
  (α ≫ β).c = (β.c ⊟ (whisker_left (opens.map β.f) α.c)) :=
rfl
end PresheafedSpace

variables {D : Type u} [𝒟 : category.{v+1} D]
include 𝒟

local attribute [simp] PresheafedSpace.id_c PresheafedSpace.comp_c presheaf.pushforward

def functor.map_presheaf (F : C ⥤ D) : PresheafedSpace.{v} C ⥤ PresheafedSpace.{v} D :=
{ obj := λ X, { X := X.X, 𝒪 := X.𝒪 ⋙ F },
  map := λ X Y f, { f := f.f, c := whisker_right f.c F } }.

@[simp] lemma functor.map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).X = X.X :=
rfl
@[simp] lemma functor.map_presheaf_obj_𝒪 (F : C ⥤ D) (X : PresheafedSpace.{v} C) :
  (F.map_presheaf.obj X).𝒪 = X.𝒪 ⋙ F :=
rfl
@[simp] lemma functor.map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).f = f.f :=
rfl
@[simp] lemma functor.map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F :=
rfl

def nat_trans.on_presheaf {F G : C ⥤ D} (α : F ⟹ G) : G.map_presheaf ⟹ F.map_presheaf :=
{ app := λ X,
  { f := 𝟙 _,
    c := whisker_left X.𝒪 α ⊟ ((functor.id_comp _).inv) ⊟ (whisker_right (opens.map_id _).inv _) },
  naturality' := λ X Y f,
  begin
    ext U,
    { cases U, -- it would be nice to do without this
      dsimp,
      simp,
      rw α.naturality,
      refl, },
    { refl, }
  end }.

end category_theory
