/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro, Reid Barton
-/
import topology.category.Top.opens

/-!
# Presheaves on a topological space

We define `presheaf C X` simply as `(opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* `pushforward_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C`
with notation `f _* ℱ`
and for `ℱ : X.presheaf C` provide the natural isomorphisms
* `pushforward.id : (𝟙 X) _* ℱ ≅ ℱ``
* `pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
along with their `@[simp]` lemmas.
-/

universes v u

open category_theory
open topological_space
open opposite

variables (C : Type u) [category.{v} C]

namespace Top

/-- The category of `C`-valued presheaves on a (bundled) topological space `X`. -/
@[derive category]
def presheaf (X : Top.{v}) := (opens X)ᵒᵖ ⥤ C

variables {C}

namespace presheaf

/-- Pushforward a presheaf on `X` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `Y`. -/
def pushforward_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
(opens.map f).op ⋙ ℱ

infix ` _* `: 80 := pushforward_obj

@[simp] lemma pushforward_obj_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) (U : (opens Y)ᵒᵖ) :
  (f _* ℱ).obj U = ℱ.obj ((opens.map f).op.obj U) := rfl

@[simp] lemma pushforward_obj_map {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C)
  {U V : (opens Y)ᵒᵖ} (i : U ⟶ V) :
  (f _* ℱ).map i = ℱ.map ((opens.map f).op.map i) := rfl

/--
An equality of continuous maps induces a natural isomorphism between the pushforwards of a presheaf
along those maps.
-/
def pushforward_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) :
  f _* ℱ ≅ g _* ℱ :=
iso_whisker_right (nat_iso.op (opens.map_iso f g h).symm) ℱ

@[simp] lemma pushforward_eq_hom_app
  {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) (U) :
  (pushforward_eq h ℱ).hom.app U =
    ℱ.map (begin dsimp [functor.op], apply quiver.hom.op, apply eq_to_hom, rw h, end) :=
by simp [pushforward_eq]

@[simp]
lemma pushforward_eq_rfl {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) (U) :
  (pushforward_eq (rfl : f = f) ℱ).hom.app (op U) = 𝟙 _ :=
begin
  dsimp [pushforward_eq],
  simp,
end

lemma pushforward_eq_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : X.presheaf C) :
  ℱ.pushforward_eq h₁ = ℱ.pushforward_eq h₂ :=
rfl

namespace pushforward
variables {X : Top.{v}} (ℱ : X.presheaf C)

/-- The natural isomorphism between the pushforward of a presheaf along the identity continuous map
and the original presheaf. -/
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

/-- The natural isomorphism between
the pushforward of a presheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward. -/
def comp {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
iso_whisker_right (nat_iso.op (opens.map_comp f g).symm) ℱ

@[simp] lemma comp_hom_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (comp ℱ f g).hom.app U = 𝟙 _ :=
by { dsimp [comp], tidy, }

@[simp] lemma comp_inv_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (comp ℱ f g).inv.app U = 𝟙 _ :=
by { dsimp [comp], tidy, }

end pushforward

/--
A morphism of presheaves gives rise to a morphisms of the pushforwards of those presheaves.
-/
@[simps]
def pushforward_map {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : X.presheaf C} (α : ℱ ⟶ 𝒢) :
  f _* ℱ ⟶ f _* 𝒢 :=
{ app := λ U, α.app _,
  naturality' := λ U V i, by { erw α.naturality, refl, } }

end presheaf

end Top
