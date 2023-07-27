/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.rigid.basic

/-!
# Transport rigid structures over a monoidal equivalence.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

noncomputable theory

namespace category_theory

variables {C D : Type*} [category C] [category D] [monoidal_category C] [monoidal_category D]
variables (F : monoidal_functor C D)

/-- Given candidate data for an exact pairing,
which is sent by a faithful monoidal functor to an exact pairing,
the equations holds automatically. -/
def exact_pairing_of_faithful [faithful F.to_functor]
  {X Y : C} (eval : Y ⊗ X ⟶ 𝟙_ C) (coeval : 𝟙_ C ⟶ X ⊗ Y)
  [exact_pairing (F.obj X) (F.obj Y)]
  (map_eval : F.map eval = inv (F.μ _ _) ≫ ε_ _ _ ≫ F.ε)
  (map_coeval : F.map coeval = inv F.ε ≫ η_ _ _  ≫ F.μ _ _) : exact_pairing X Y :=
{ evaluation := eval,
  coevaluation := coeval,
  evaluation_coevaluation' := F.to_functor.map_injective
    (by simp [map_eval, map_coeval, monoidal_functor.map_tensor]),
  coevaluation_evaluation' := F.to_functor.map_injective
    (by simp [map_eval, map_coeval, monoidal_functor.map_tensor]), }

/--
Given a pair of objects which are sent by a fully faithful functor to a pair of objects
with an exact pairing, we get an exact pairing.
-/
def exact_pairing_of_fully_faithful [full F.to_functor] [faithful F.to_functor] (X Y : C)
  [exact_pairing (F.obj X) (F.obj Y)] : exact_pairing X Y :=
exact_pairing_of_faithful F
  (F.to_functor.preimage (inv (F.μ _ _) ≫ ε_ _ _ ≫ F.ε))
  (F.to_functor.preimage (inv F.ε ≫ η_ _ _ ≫ F.μ _ _))
  (by simp) (by simp)

/-- Pull back a left dual along an equivalence. -/
def has_left_dual_of_equivalence [is_equivalence F.to_functor] (X : C) [has_left_dual (F.obj X)] :
  has_left_dual X :=
{ left_dual := F.to_functor.inv.obj (ᘁ(F.obj X)),
  exact := begin
    apply exact_pairing_of_fully_faithful F _ _,
    apply exact_pairing_congr_left (F.to_functor.as_equivalence.counit_iso.app _),
    dsimp,
    apply_instance,
  end }

/-- Pull back a right dual along an equivalence. -/
def has_right_dual_of_equivalence [is_equivalence F.to_functor] (X : C) [has_right_dual (F.obj X)] :
  has_right_dual X :=
{ right_dual := F.to_functor.inv.obj (F.obj X)ᘁ,
  exact := begin
    apply exact_pairing_of_fully_faithful F _ _,
    apply exact_pairing_congr_right (F.to_functor.as_equivalence.counit_iso.app _),
    dsimp,
    apply_instance,
  end }

/-- Pull back a left rigid structure along an equivalence. -/
def left_rigid_category_of_equivalence [is_equivalence F.to_functor]
  [left_rigid_category D] : left_rigid_category C :=
{ left_dual := λ X, has_left_dual_of_equivalence F X, }

/-- Pull back a right rigid structure along an equivalence. -/
def right_rigid_category_of_equivalence [is_equivalence F.to_functor]
  [right_rigid_category D] : right_rigid_category C :=
{ right_dual := λ X, has_right_dual_of_equivalence F X, }

/-- Pull back a rigid structure along an equivalence. -/
def rigid_category_of_equivalence [is_equivalence F.to_functor]
  [rigid_category D] : rigid_category C :=
{ left_dual := λ X, has_left_dual_of_equivalence F X,
  right_dual := λ X, has_right_dual_of_equivalence F X, }

end category_theory
