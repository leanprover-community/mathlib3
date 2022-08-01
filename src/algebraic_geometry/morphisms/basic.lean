/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.AffineScheme
import algebraic_geometry.pullbacks
import category_theory.morphism_property

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

-/

universe u

open topological_space category_theory category_theory.limits opposite

noncomputable theory

namespace algebraic_geometry

/-- An `affine_target_morphism_property` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def affine_target_morphism_property := ∀ ⦃X Y : Scheme⦄ (f : X ⟶ Y) [is_affine Y], Prop

/-- `is_iso` as a `morphism_property`. -/
protected def Scheme.is_iso : morphism_property Scheme := @is_iso Scheme _

/-- `is_iso` as an `affine_morphism_property`. -/
protected def Scheme.affine_target_is_iso : affine_target_morphism_property :=
λ X Y f H, is_iso f

instance : inhabited affine_target_morphism_property := ⟨Scheme.affine_target_is_iso⟩

/-- A `affine_target_morphism_property` can be extended to a `morphism_property` such that it
*never* holds when the target is not affine -/
def affine_target_morphism_property.to_property (P : affine_target_morphism_property) :
  morphism_property Scheme :=
λ X Y f, ∃ h, @@P f h

lemma affine_target_morphism_property.to_property_apply (P : affine_target_morphism_property)
  {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  P.to_property f ↔ P f := by { delta affine_target_morphism_property.to_property, simv [*] }

end algebraic_geometry
