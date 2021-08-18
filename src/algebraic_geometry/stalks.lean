/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space
import category_theory.limits.final
import topology.sheaves.stalks

/-!
# Stalks for presheaved spaces

This file lifts constructions of stalks and pushforwards of stalks to work with
the category of presheafed spaces.
-/

noncomputable theory

universes v u v' u'

open category_theory
open category_theory.limits category_theory.category category_theory.functor
open algebraic_geometry
open topological_space
open opposite

variables {C : Type u} [category.{v} C] [has_colimits C]

local attribute [tidy] tactic.op_induction'

open Top.presheaf

namespace algebraic_geometry.PresheafedSpace

/--
The stalk at `x` of a `PresheafedSpace`.
-/
def stalk (X : PresheafedSpace C) (x : X) : C := X.presheaf.stalk x

/--
A morphism of presheafed spaces induces a morphism of stalks.
-/
def stalk_map {X Y : PresheafedSpace C} (α : X ⟶ Y) (x : X) : Y.stalk (α.base x) ⟶ X.stalk x :=
(stalk_functor C (α.base x)).map (α.c) ≫ X.presheaf.stalk_pushforward C α.base x

@[simp, elementwise, reassoc]
lemma stalk_map_germ {X Y : PresheafedSpace C} (α : X ⟶ Y) (U : opens Y.carrier)
  (x : (opens.map α.base).obj U) :
  Y.presheaf.germ ⟨α.base x, x.2⟩ ≫ stalk_map α ↑x = α.c.app (op U) ≫ X.presheaf.germ x :=
by rw [stalk_map, stalk_functor_map_germ_assoc, stalk_pushforward_germ]

section restrict

def restrict_stalk_iso {U : Top} (X : PresheafedSpace C)
  (f : U ⟶ (X : Top.{v})) (h : open_embedding f) (x : U) :
  (X.restrict f h).stalk x ≅ X.stalk (f x) :=
begin
  change colimit ((h.is_open_map.functor_nhds x).op ⋙ (open_nhds.inclusion (f x)).op ⋙ X.presheaf)
    ≅ colimit ((open_nhds.inclusion (f x)).op ⋙ X.presheaf),
  -- As a left adjoint, the functor `h.is_open_map.functor_nhds x` is initial.
  haveI := functor.initial_of_left_adjoint (h.is_open_map.adjunction_nhds x),
  -- Typeclass resolution knows that the dual of an initial functor is final. The result follows
  -- from the general fact that postcomposing with a final functor doesn't change colimits.
  apply functor.final.colimit_iso,
end


-- TODO `restrict_stalk_iso` is compatible with `germ`.


end restrict

namespace stalk_map

@[simp] lemma id (X : PresheafedSpace C) (x : X) : stalk_map (𝟙 X) x = 𝟙 (X.stalk x) :=
begin
  dsimp [stalk_map],
  simp only [stalk_pushforward.id],
  rw [←map_comp],
  convert (stalk_functor C x).map_id X.presheaf,
  tidy,
end

-- TODO understand why this proof is still gross (i.e. requires using `erw`)
@[simp] lemma comp {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
  stalk_map (α ≫ β) x =
    (stalk_map β (α.base x) : Z.stalk (β.base (α.base x)) ⟶ Y.stalk (α.base x)) ≫
    (stalk_map α x : Y.stalk (α.base x) ⟶ X.stalk x) :=
begin
  dsimp [stalk_map, stalk_functor, stalk_pushforward],
  ext U,
  op_induction U,
  cases U,
  simp only [colimit.ι_map_assoc, colimit.ι_pre_assoc, colimit.ι_pre,
    whisker_left_app, whisker_right_app,
    assoc, id_comp, map_id, map_comp],
  dsimp,
  simp only [map_id, assoc, pushforward.comp_inv_app],
  -- FIXME Why doesn't simp do this:
  erw [category_theory.functor.map_id],
  erw [category_theory.functor.map_id],
  erw [id_comp, id_comp, id_comp],
end
end stalk_map

end algebraic_geometry.PresheafedSpace
