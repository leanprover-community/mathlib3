-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Mario Carneiro, Reid Barton

import category_theory.instances.Top.opens
import category_theory.whiskering
import category_theory.natural_isomorphism

universes v u

open category_theory
open category_theory.instances
open topological_space

namespace algebraic_geometry

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

def presheaf_on_space (X : Top.{v}) := (opens X)ᵒᵖ ⥤ C

instance category_presheaf_on_space (X : Top.{v}) : category (presheaf_on_space C X) :=
by dsimp [presheaf_on_space]; apply_instance

namespace presheaf_on_space
variables {C}

def pushforward {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : presheaf_on_space C X) : presheaf_on_space C Y :=
(opens.map f).op ⋙ ℱ

def pushforward_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : presheaf_on_space C X) :
  ℱ.pushforward f ≅ ℱ.pushforward g :=
iso_whisker_right (nat_iso.op (opens.map_iso f g h).symm) ℱ
lemma pushforward_eq_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : presheaf_on_space C X) :
  ℱ.pushforward_eq h₁ = ℱ.pushforward_eq h₂ :=
rfl

namespace pushforward
def id {X : Top.{v}} (ℱ : presheaf_on_space C X) : ℱ.pushforward (𝟙 X) ≅ ℱ :=
(iso_whisker_right (nat_iso.op (opens.map_id X).symm) ℱ) ≪≫ functor.left_unitor _

@[simp] lemma id_hom_app' {X : Top.{v}} (ℱ : presheaf_on_space C X) (U) (p) : (id ℱ).hom.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, dsimp, simp }

@[simp] lemma id_hom_app {X : Top.{v}} (ℱ : presheaf_on_space C X) (U) : (id ℱ).hom.app U = ℱ.map (eq_to_hom (opens.op_map_id_obj U)) :=
begin
  have w : U = op (unop U) := rfl,
  revert w,
  generalize : unop U = U',
  intro w,
  subst w,
  cases U',
  simp,
  erw category_theory.functor.map_id,
end

@[simp] lemma id_inv_app' {X : Top.{v}} (ℱ : presheaf_on_space C X) (U) (p) : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, dsimp, simp }

def comp {X Y Z : Top.{v}}  (ℱ : presheaf_on_space C X) (f : X ⟶ Y) (g : Y ⟶ Z) : ℱ.pushforward (f ≫ g) ≅ (ℱ.pushforward f).pushforward g :=
iso_whisker_right (nat_iso.op (opens.map_comp f g).symm) ℱ

@[simp] lemma comp_hom_app {X Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : presheaf_on_space C X) (U) : (comp ℱ f g).hom.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  simp,
  erw category_theory.functor.map_id, -- FIXME simp should do this
  dsimp,
  simp,
end
@[simp] lemma comp_inv_app {X Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : presheaf_on_space C X) (U) : (comp ℱ f g).inv.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  simp,
  erw category_theory.functor.map_id,
  dsimp,
  simp,
end

end pushforward

end presheaf_on_space

end algebraic_geometry
