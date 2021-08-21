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
the category of presheafed spaces. Additionally, we prove that restriction of
presheafed spaces does not change the stalks.
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

/--
For an open embedding `f : U ⟶ X` and a point `x : U`, we get an isomorphism between the stalk
of `X` at `f x` and the stalk of the restriction of `X` along `f` at t `x`.
-/
def restrict_stalk_iso {U : Top} (X : PresheafedSpace C)
  (f : U ⟶ (X : Top.{v})) (h : open_embedding f) (x : U) :
  (X.restrict f h).stalk x ≅ X.stalk (f x) :=
begin
  -- As a left adjoint, the functor `h.is_open_map.functor_nhds x` is initial.
  haveI := initial_of_adjunction (h.is_open_map.adjunction_nhds x),
  -- Typeclass resolution knows that the opposite of an initial functor is final. The result
  -- follows from the general fact that postcomposing with a final functor doesn't change colimits.
  exact final.colimit_iso (h.is_open_map.functor_nhds x).op
    ((open_nhds.inclusion (f x)).op ⋙ X.presheaf),
end

@[simp, elementwise, reassoc]
lemma restrict_stalk_iso_hom_germ {U : Top} (X : PresheafedSpace C) (f : U ⟶ (X : Top.{v}))
  (h : open_embedding f) (V : opens U) (x : U) (hx : x ∈ V) :
  (X.restrict f h).presheaf.germ ⟨x, hx⟩ ≫ (restrict_stalk_iso X f h x).hom =
  X.presheaf.germ ⟨f x, show f x ∈ h.is_open_map.functor.obj V, from ⟨x, hx, rfl⟩⟩ :=
colimit.ι_pre ((open_nhds.inclusion (f x)).op ⋙ X.presheaf)
  (h.is_open_map.functor_nhds x).op (op ⟨V, hx⟩)

@[simp, elementwise, reassoc]
lemma restrict_stalk_iso_inv_germ {U : Top} (X : PresheafedSpace C) (f : U ⟶ (X : Top.{v}))
  (h : open_embedding f) (V : opens U) (x : U) (hx : x ∈ V) :
  X.presheaf.germ ⟨f x, show f x ∈ h.is_open_map.functor.obj V, from ⟨x, hx, rfl⟩⟩ ≫
  (restrict_stalk_iso X f h x).inv = (X.restrict f h).presheaf.germ ⟨x, hx⟩ :=
by rw [← restrict_stalk_iso_hom_germ, category.assoc, iso.hom_inv_id, category.comp_id]

/--
For an open embedding `f : U ⟶ X`, the induced stalk map of the canonical inclusion
`X.restrict f _ ⟶ X` is equal to the isomorphism of stalks defined above.
In particular, it is an isomorphism.
-/
lemma stalk_map_of_restrict_eq {U : Top} (X : PresheafedSpace C) (f : U ⟶ (X : Top.{v}))
  (h : open_embedding f) (x : U) :
  stalk_map (X.of_restrict f h) x = (X.restrict_stalk_iso f h x).inv :=
stalk_hom_ext _ $ λ V hx,
begin
  -- The canonical inclusion morphism `f '' (f ⁻¹ V) ⟶ V`.
  -- This will be filled in automatically by unification later.
  let i : h.is_open_map.functor.obj ((opens.map f).obj V) ⟶ V := _,
  erw [stalk_map_germ (X.of_restrict f h) V ⟨x, hx⟩, ← germ_res X.presheaf i ⟨f x, ⟨x, hx, rfl⟩⟩,
    category.assoc, restrict_stalk_iso_inv_germ X f h ((opens.map f).obj V) x hx],
  congr,
end

instance is_iso_stalk_map_of_restrict {U : Top} (X : PresheafedSpace C) (f : U ⟶ (X : Top.{v}))
  (h : open_embedding f) (x : U) :
  is_iso (stalk_map (X.of_restrict f h) x) :=
by { rw stalk_map_of_restrict_eq, apply_instance }

/--
The induced stalk map of the canonical map `X ⟶ X.restrict (opens.inclusion ⊤) _` is equal to the
isomorphism of stalks defined above.
In particular, it is an isomorphism.
-/
lemma stalk_map_to_restrict_top (X : PresheafedSpace C) (x : X) :
  stalk_map X.to_restrict_top x =
  (restrict_stalk_iso X (opens.inclusion ⊤) (opens.open_embedding ⊤) ⟨x, trivial⟩).hom :=
stalk_hom_ext _ $ λ U hx,
begin
  erw [stalk_map_germ X.to_restrict_top U ⟨x, hx⟩, restrict_stalk_iso_hom_germ X _ _ U ⟨x, trivial⟩,
    germ_res],
  congr,
end

instance is_iso_stalk_map_to_restrict_top (X : PresheafedSpace C) (x : X) :
  is_iso (stalk_map X.to_restrict_top x) :=
by { rw stalk_map_to_restrict_top, apply_instance }

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
