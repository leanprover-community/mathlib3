/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import topology.category.TopCommRing
import topology.algebra.continuous_functions

universes v u

open category_theory
open topological_space
open opposite

namespace Top

variables (X Y : Top.{v})

def presheaf_to_Type (T : Type v) : X.presheaf (Type v) :=
(opens.to_Top X ⋙ forget Top).op ⋙ (yoneda.obj T)

/-- The presheaf of continuous functions on `X` with values in fixed target topological space `T`. -/
def presheaf_to_Top (T : Top.{v}) : X.presheaf (Type v) :=
(opens.to_Top X).op ⋙ (yoneda.obj T)

/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
-- TODO upgrade the result to TopCommRing?
def continuous_functions (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) : CommRing.{v} :=
CommRing.of (unop X ⟶ (forget₂ TopCommRing Top).obj R)

namespace continuous_functions

/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
def pullback {X Y : Topᵒᵖ} (f : X ⟶ Y) (R : TopCommRing) :
  continuous_functions X R ⟶ continuous_functions Y R :=
{ to_fun := λ g, f.unop ≫ g,
  map_one' := rfl,
  map_zero' := rfl,
  map_add' := by tidy,
  map_mul' := by tidy }

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : Top.{u}ᵒᵖ) {R S : TopCommRing.{u}} (φ : R ⟶ S) :
  continuous_functions X R ⟶ continuous_functions X S :=
{ to_fun := λ g, g ≫ ((forget₂ TopCommRing Top).map φ),
  map_one' := by ext; exact φ.1.map_one,
  map_zero' := by ext; exact φ.1.map_zero,
  map_add' := by intros; ext; apply φ.1.map_add,
  map_mul' := by intros; ext; apply φ.1.map_mul }
end continuous_functions

/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : Top` to `R : TopCommRing` form a commutative ring, functorial in both `X` and `R`. -/
def CommRing_yoneda : TopCommRing.{u} ⥤ (Top.{u}ᵒᵖ ⥤ CommRing.{u}) :=
{ obj := λ R,
  { obj := λ X, continuous_functions X R,
    map := λ X Y f, continuous_functions.pullback f R },
  map := λ R S φ,
  { app := λ X, continuous_functions.map X φ } }

/-- The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`. -/
def presheaf_to_TopCommRing (T : TopCommRing.{v}) :
  X.presheaf CommRing.{v} :=
(opens.to_Top X).op ⋙ (CommRing_yoneda.obj T)

/-- The presheaf (of commutative rings) of real valued functions. -/
noncomputable def presheaf_ℝ (Y : Top) : Y.presheaf CommRing :=
presheaf_to_TopCommRing Y (TopCommRing.of ℝ)

/-- The presheaf (of commutative rings) of complex valued functions. -/
noncomputable def presheaf_ℂ (Y : Top) : Y.presheaf CommRing :=
presheaf_to_TopCommRing Y (TopCommRing.of ℂ)

end Top
