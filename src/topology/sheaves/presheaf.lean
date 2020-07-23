/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro, Reid Barton
-/
import topology.category.Top.opens

universes v u

open category_theory
open topological_space
open opposite

variables (C : Type u) [category.{v} C]

namespace Top

@[derive category]
def presheaf (X : Top.{v}) := (opens X)ᵒᵖ ⥤ C

namespace presheaf
variables {C}

def pushforward {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
(opens.map f).op ⋙ ℱ

infix ` _* `: 80 := pushforward

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

local attribute [tidy] tactic.op_induction'

@[simp, priority 990] lemma id_hom_app (U) :
  (id ℱ).hom.app U = ℱ.map (eq_to_hom (opens.op_map_id_obj U)) := by tidy

@[simp] lemma id_inv_app' (U) (p) : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, }

def comp {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
iso_whisker_right (nat_iso.op (opens.map_comp f g).symm) ℱ

@[simp] lemma comp_hom_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).hom.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  tidy,
end

@[simp] lemma comp_inv_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).inv.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  tidy,
end

end pushforward

end presheaf

end Top
