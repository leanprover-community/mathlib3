/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf
import category_theory.limits.preserves.shapes
import category_theory.limits.types

/-!
# Checking the sheaf condition on the underlying presheaf of types.

When `C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphism,
the sheaf condition for a `C`-valued presheaf is equivalent to
the sheaf condition for the underlying `Type`-valued presheaf.

## References
* https://stacks.math.columbia.edu/tag/0073
-/

open category_theory
open category_theory.limits
open topological_space
open opposite


namespace Top

namespace sheaf_condition

universes v u

variables {C : Type u} [category.{v} C] [has_limits C]
variables {D : Type u} [category.{v} D] [has_limits D]
variables (G : C ⥤ D) [preserves_limits G]
variables {X : Top.{v}} (F : presheaf C X)
variables {ι : Type v} (U : ι → opens X)

local attribute [reducible] sheaf_condition.diagram
local attribute [reducible] sheaf_condition.left_res sheaf_condition.right_res

/--
When `G` preserves limits, the sheaf condition diagram for `F` composed with `G` is
naturally isomorphic to the sheaf condition diagram for `F ⋙ G`.
-/
def diagram_comp_preserves_limits :
  sheaf_condition.diagram F U ⋙ G ≅ sheaf_condition.diagram (F ⋙ G) U :=
begin
  fapply nat_iso.of_components,
  intro j,
  cases j,
  exact (preserves_products_iso _ _),
  exact (preserves_products_iso _ _),
  intros j j' f,
  cases j; cases j'; cases f,
  { ext, simp, dsimp, simp, }, -- non-terminal `simp`, but `squeeze_simp` fails
  { ext,
    simp only [limit.lift_π, functor.comp_map, parallel_pair_map_left, fan.mk_π_app,
      lift_comp_preserves_products_iso_hom, functor.map_comp, category.assoc],
    dsimp, simp, },
  { ext,
    simp only [limit.lift_π, functor.comp_map, parallel_pair_map_right, fan.mk_π_app,
      lift_comp_preserves_products_iso_hom, functor.map_comp, category.assoc],
    dsimp, simp, },
 { ext, simp, dsimp, simp, },
end

local attribute [reducible] sheaf_condition.res

/--
When `G` preserves limits, the image under `G` of the sheaf condition fork for `F`
is the sheaf condition fork for `F ⋙ G`,
postcomposed with the inverse of the natural isomorphism `diagram_comp_preserves_limits`.
-/
def map_cone_fork : G.map_cone (sheaf_condition.fork F U) ≅
  (cones.postcompose (diagram_comp_preserves_limits G F U).inv).obj
    (sheaf_condition.fork (F ⋙ G) U) :=
cones.ext (iso.refl _) (λ j,
begin
  dsimp, simp [diagram_comp_preserves_limits], cases j; dsimp,
  { rw iso.eq_comp_inv,
    ext,
    simp, dsimp, simp, },
  { rw iso.eq_comp_inv,
    ext,
    simp, -- non-terminal `simp`, but `squeeze_simp` fails
    dsimp,
    simp only [limit.lift_π, fan.mk_π_app],
    simp only [←G.map_comp],
    simp only [limit.lift_π_assoc, fan.mk_π_app],
  },
end)

end sheaf_condition

universes v u

open sheaf_condition

variables {C : Type (u+1)} [large_category C] [concrete_category C]
variables [reflects_isomorphisms (forget C)]
variables [has_limits C] [preserves_limits (forget C)]

variables {X : Top.{u}} (F : presheaf C X)

-- This is often a good `simp` lemma, but it breaks this proof.
-- It would be nice to either remove it as a simp lemma, or make the proof below more robust.
local attribute [-simp] forget_map_eq_coe

/--
If `C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms,
to check the sheaf condition it suffices to check it on the underlying sheaf of types.
-/
def sheaf_condition_equiv_sheaf_condition_forget :
  sheaf_condition F ≃ sheaf_condition (F ⋙ (forget C)) :=
begin
  fsplit,
  { intros S ι U,
    -- We have that the sheaf condition fork for `F` is a limit fork,
    have t₁ := S U,
    -- and since `forget C` preserves limits, the image under `G` of these fork is a limit fork to.
    have t₂ := @preserves_limit.preserves _ _ _ _ _ _ _ (forget C) _ _ t₁,
    -- As we established above, that image is just the sheaf condition fork
    -- for `F ⋙ forget C` postcomposed with some natural isomorphism,
    have t₃ := is_limit.of_iso_limit t₂ (map_cone_fork _ _ _),
    -- and as postcomposing by a natural isomorphism preserves limit cones,
    have t₄ := is_limit.postcompose_inv_equiv _ _ t₃,
    -- we have our desired conclusion.
    exact t₄, },
  { intros S ι U,
    -- Let `f` be the universal morphism from `F.obj U` to the equalizer of the sheaf condition fork,
    -- whatever it is. Our goal is to show that this is an isomorphism.
    let f := equalizer.lift _ (w F U),
    -- If we can do that,
    suffices : is_iso ((forget C).map f),
    { resetI,
      -- we have that `f` itself is an isomorphism, since `forget C` reflects isomorphisms
      haveI : is_iso f := is_iso_of_reflects_iso f (forget C),
      -- TODO package this up as a result elsewhere:
      apply is_limit.of_iso_limit (limit.is_limit _),
      apply iso.symm,
      fapply cones.ext,
      exact (as_iso f),
      rintro ⟨_|_⟩; { dsimp [f], simp, }, },
    { -- Returning to the task of shwoing that `(forget C).map f` is an isomorphism,
      -- we note that `(forget C).map f` is almost but not quite (see below) a morphism
      -- from the sheaf condition cone for `F ⋙ forget C` to the
      -- image under `forget C` of the equalizer cone for the sheaf condition diagram.
      let c := sheaf_condition.fork (F ⋙ forget C) U,
      have hc : is_limit c := S U,
      let d := (forget C).map_cone (equalizer.fork (left_res F U) (right_res F U)),
      have hd : is_limit d := preserves_limit.preserves (limit.is_limit _),
      -- Since both of these are limit cones
      -- (`c` by our hypothesis `S`, and `d` because `forget C` preserves limits),
      -- we hope to be able to conclude that `f` is a isomorphism.
      -- We say "not quite" above because `c` and `d` don't quite have the same shape:
      -- we need to postcompose by the natural isomorphism `diagram_comp_preserves_limits`
      -- introduced above.
      let d' := (cones.postcompose (diagram_comp_preserves_limits _ F U).hom).obj d,
      have hd' : is_limit d' :=
        (is_limit.postcompose_hom_equiv.{u} (diagram_comp_preserves_limits (forget C) F U) _).symm hd,
      -- Now everything works: we verify that `f` really is a morphism between these cones:
      let f' : c ⟶ d' :=
      fork.mk_hom ((forget C).map f)
      begin
        dsimp only [c, d, d', f, diagram_comp_preserves_limits, res],
        dunfold fork.ι,
        ext1 j,
        dsimp,
        simp only [category.assoc],
        simp only [←functor.map_comp_assoc],
        simp only [equalizer.lift_ι, lift_comp_preserves_products_iso_hom_assoc],
        dsimp [res], simp,
      end,
      -- conclude that it is an isomorphism,
      -- just because it's a morphism between two limit cones.
      haveI : is_iso f' := is_limit.hom_is_iso hc hd' f',
      -- A cone morphism is an isomorphism exactly if the morphism between the cone points is,
      -- so we're done!
      exact { ..((cones.forget _).map_iso (as_iso f')) }, }, },
  { intros S, apply subsingleton.elim, },
  { intros S, apply subsingleton.elim, },
end

/-!
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.
```
example (X : Top) (F : presheaf CommRing X) (h : sheaf_condition (F ⋙ (forget CommRing))) :
  sheaf_condition F :=
(sheaf_condition_equiv_sheaf_condition_forget F).symm h
```
-/

end Top
