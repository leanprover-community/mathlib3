/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import topology.category.TopCommRing
import category_theory.yoneda
import ring_theory.subring
import topology.algebra.continuous_functions

universes v u

open category_theory
open topological_space
open opposite

namespace Top

variables (X : Top.{v})

def presheaf_to_Top (T : Top.{v}) : X.presheaf (Type v) :=
(opens.to_Top X).op ⋙ (yoneda.obj T)

-- TODO upgrade the result to TopCommRing?
def continuous_functions (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) : CommRing.{v} :=
{ α := unop X ⟶ (forget₂ TopCommRing Top).obj R,
  str := _root_.continuous_comm_ring }

namespace continuous_functions
@[simp] lemma one (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (x) :
  (monoid.one ↥(continuous_functions X R)).val x = 1 := rfl
@[simp] lemma zero (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (x) :
  (comm_ring.zero ↥(continuous_functions X R)).val x = 0 := rfl
@[simp] lemma add (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (f g : continuous_functions X R) (x) :
  (comm_ring.add f g).val x = f.1 x + g.1 x := rfl
@[simp] lemma mul (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (f g : continuous_functions X R) (x) :
  (ring.mul f g).val x = f.1 x * g.1 x := rfl

def pullback {X Y : Topᵒᵖ} (f : X ⟶ Y) (R : TopCommRing) :
  continuous_functions X R ⟶ continuous_functions Y R :=
{ to_fun := λ g, f.unop ≫ g,
  map_one' := rfl,
  map_zero' := rfl,
  map_add' := by tidy,
  map_mul' := by tidy }

local attribute [extensionality] subtype.eq

def map (X : Topᵒᵖ) {R S : TopCommRing} (φ : R ⟶ S) :
  continuous_functions X R ⟶ continuous_functions X S :=
{ to_fun := λ g, g ≫ ((forget₂ TopCommRing Top).map φ),
  map_one' := by ext; exact φ.1.map_one,
  map_zero' := by ext; exact φ.1.map_zero,
  map_add' := by intros; ext; apply φ.1.map_add,
  map_mul' := by intros; ext; apply φ.1.map_mul }
end continuous_functions

def CommRing_yoneda : TopCommRing.{u} ⥤ (Top.{u}ᵒᵖ ⥤ CommRing.{u}) :=
{ obj := λ R,
  { obj := λ X, continuous_functions X R,
    map := λ X Y f, continuous_functions.pullback f R },
  map := λ R S φ,
  { app := λ X, continuous_functions.map X φ } }

def presheaf_to_TopCommRing (T : TopCommRing.{v}) :
  X.presheaf CommRing.{v} :=
(opens.to_Top X).op ⋙ (CommRing_yoneda.obj T)

noncomputable def presheaf_ℝ (Y : Top) : Y.presheaf CommRing :=
presheaf_to_TopCommRing Y (TopCommRing.of ℝ)

noncomputable def presheaf_ℂ (Y : Top) : Y.presheaf CommRing :=
presheaf_to_TopCommRing Y (TopCommRing.of ℂ)

end Top
