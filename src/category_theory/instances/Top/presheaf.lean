-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Mario Carneiro, Reid Barton

import category_theory.instances.Top.opens
import category_theory.whiskering

universes v u

open category_theory
open category_theory.instances
open topological_space

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

namespace category_theory.instances.Top

def presheaf (X : Top.{v}) := (opens X)ᵒᵖ ⥤ C

instance category_presheaf (X : Top.{v}) : category (X.presheaf C) :=
by dsimp [presheaf]; apply_instance

namespace presheaf
variables {C}

def pushforward {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
(opens.map f).op ⋙ ℱ

infix `_*`: 80 := pushforward

def pushforward_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) :
  f _* ℱ ≅ g _* ℱ :=
iso_whisker_right (nat_iso.op (opens.map_iso f g h).symm) ℱ
lemma pushforward_eq_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : X.presheaf C) :
  ℱ.pushforward_eq h₁ = ℱ.pushforward_eq h₂ :=
rfl

namespace pushforward
variables {X : Top.{v}} (ℱ : X.presheaf C)

def id : (𝟙 X) _* ℱ ≅ ℱ :=
(iso_whisker_right (nat_iso.op (opens.map_id X).symm) ℱ) ≪≫ functor.left_unitor _

@[simp] lemma id_hom_app' (U) (p) :
  (id ℱ).hom.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, }

@[simp] lemma id_hom_app (U) :
  (id ℱ).hom.app U = ℱ.map (eq_to_hom (opens.op_map_id_obj U)) :=
begin
  op_induction U,
  cases U,
  simp,
  apply category_theory.functor.map_id,
end

@[simp] lemma id_inv_app' (U) (p) : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, }

def comp {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
iso_whisker_right (nat_iso.op (opens.map_comp f g).symm) ℱ

@[simp] lemma comp_hom_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).hom.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  erw category_theory.functor.map_id, -- FIXME simp should do this
end

@[simp] lemma comp_inv_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).inv.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  erw category_theory.functor.map_id,
end

end pushforward

end presheaf

end category_theory.instances.Top
