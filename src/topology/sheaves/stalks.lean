/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.category.Top.open_nhds
import topology.sheaves.presheaf
import category_theory.limits.limits

universes v u v' u'

open category_theory
open Top
open category_theory.limits
open topological_space

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables [has_colimits.{v} C]

variables {X Y Z : Top.{v}}

namespace Top.presheaf

variables (C)
/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalk_functor (x : X) : X.presheaf C ⥤ C :=
((whiskering_left _ _ C).obj (open_nhds.inclusion x).op) ⋙ colim

variables {C}

/--
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.presheaf C) (x : X) : C :=
(stalk_functor C x).obj ℱ -- -- colimit (nbhds_inclusion x ⋙ ℱ)

@[simp] lemma stalk_functor_obj (ℱ : X.presheaf C) (x : X) : (stalk_functor C x).obj ℱ = ℱ.stalk x := rfl

variables (C)

def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
begin
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  transitivity,
  swap,
  exact colimit.pre _ (open_nhds.map f x).op,
  exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ),
end

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240
-- However, I can't get the subsequent two proofs to work with either one.

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((functor.associator _ _ _).inv ≫
--   whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- (colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) :
--   colim.obj ((open_nhds.inclusion (f x) ⋙ opens.map f).op ⋙ ℱ) ⟶ _) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

namespace stalk_pushforward
local attribute [tidy] tactic.op_induction'

@[simp] lemma id (ℱ : X.presheaf C) (x : X) :
  ℱ.stalk_pushforward C (𝟙 X) x = (stalk_functor C x).map ((pushforward.id ℱ).hom) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  ext1,
  tactic.op_induction',
  cases j, cases j_val,
  rw [colim.ι_map_assoc, colim.ι_map, colimit.ι_pre, whisker_left.app, whisker_right.app,
       pushforward.id_hom_app, eq_to_hom_map, eq_to_hom_refl],
  dsimp,
  rw [category_theory.functor.map_id]
end

@[simp] lemma comp (ℱ : X.presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  ℱ.stalk_pushforward C (f ≫ g) x =
  ((f _* ℱ).stalk_pushforward C g (f x)) ≫ (ℱ.stalk_pushforward C f x) :=
begin
  dsimp [stalk_pushforward, stalk_functor, pushforward],
  ext U,
  op_induction U,
  cases U,
  cases U_val,
  simp only [colim.ι_map_assoc, colimit.ι_pre_assoc, colimit.ι_pre,
             whisker_right.app, category.assoc],
  dsimp,
  simp only [category.id_comp, category_theory.functor.map_id],
  -- FIXME A simp lemma which unfortunately doesn't fire:
  rw [category_theory.functor.map_id],
  dsimp,
  simp,
end

end stalk_pushforward
end Top.presheaf
