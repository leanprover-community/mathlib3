/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf
import category_theory.limits.preserves.shapes.products
import category_theory.limits.types

/-!
# Checking the sheaf condition on the underlying presheaf of types.

If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices
to check it on the underlying sheaf of types.

## References
* https://stacks.math.columbia.edu/tag/0073
-/

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

namespace presheaf

namespace sheaf_condition

open sheaf_condition_equalizer_products

universes v u₁ u₂

variables {C : Type u₁} [category.{v} C] [has_limits C]
variables {D : Type u₂} [category.{v} D] [has_limits D]
variables (G : C ⥤ D) [preserves_limits G]
variables {X : Top.{v}} (F : presheaf C X)
variables {ι : Type v} (U : ι → opens X)

local attribute [reducible] diagram left_res right_res

/--
When `G` preserves limits, the sheaf condition diagram for `F` composed with `G` is
naturally isomorphic to the sheaf condition diagram for `F ⋙ G`.
-/
def diagram_comp_preserves_limits :
  diagram F U ⋙ G ≅ diagram (F ⋙ G) U :=
begin
  fapply nat_iso.of_components,
  rintro ⟨j⟩,
  exact (preserves_product.iso _ _),
  exact (preserves_product.iso _ _),
  rintros ⟨⟩ ⟨⟩ ⟨⟩,
  { ext, simp, dsimp, simp, }, -- non-terminal `simp`, but `squeeze_simp` fails
  { ext,
    simp only [limit.lift_π, functor.comp_map, map_lift_pi_comparison, fan.mk_π_app,
               preserves_product.iso_hom, parallel_pair_map_left, functor.map_comp,
               category.assoc],
    dsimp, simp, },
  { ext,
    simp only [limit.lift_π, functor.comp_map, parallel_pair_map_right, fan.mk_π_app,
               preserves_product.iso_hom, map_lift_pi_comparison, functor.map_comp,
               category.assoc],
    dsimp, simp, },
 { ext, simp, dsimp, simp, },
end

local attribute [reducible] res

/--
When `G` preserves limits, the image under `G` of the sheaf condition fork for `F`
is the sheaf condition fork for `F ⋙ G`,
postcomposed with the inverse of the natural isomorphism `diagram_comp_preserves_limits`.
-/
def map_cone_fork : G.map_cone (fork F U) ≅
  (cones.postcompose (diagram_comp_preserves_limits G F U).inv).obj (fork (F ⋙ G) U) :=
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
    simp only [limit.lift_π, fan.mk_π_app, ←G.map_comp, limit.lift_π_assoc, fan.mk_π_app] }
end)

end sheaf_condition

universes v u₁ u₂

open sheaf_condition sheaf_condition_equalizer_products

variables {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)
variables [reflects_isomorphisms G]
variables [has_limits C] [has_limits D] [preserves_limits G]

variables {X : Top.{v}} (F : presheaf C X)

/--
If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices to check it on the underlying sheaf of types.

Another useful example is the forgetful functor `TopCommRing ⥤ Top`.

See https://stacks.math.columbia.edu/tag/0073.
In fact we prove a stronger version with arbitrary complete target category.
-/
lemma is_sheaf_iff_is_sheaf_comp :
  presheaf.is_sheaf F ↔ presheaf.is_sheaf (F ⋙ G) :=
begin
  split,
  { intros S ι U,
    -- We have that the sheaf condition fork for `F` is a limit fork,
    obtain ⟨t₁⟩ := S U,
    -- and since `G` preserves limits, the image under `G` of this fork is a limit fork too.
    have t₂ := @preserves_limit.preserves _ _ _ _ _ _ _ G _ _ t₁,
    -- As we established above, that image is just the sheaf condition fork
    -- for `F ⋙ G` postcomposed with some natural isomorphism,
    have t₃ := is_limit.of_iso_limit t₂ (map_cone_fork G F U),
    -- and as postcomposing by a natural isomorphism preserves limit cones,
    have t₄ := is_limit.postcompose_inv_equiv _ _ t₃,
    -- we have our desired conclusion.
    exact ⟨t₄⟩, },
  { intros S ι U,
    refine ⟨_⟩,
    -- Let `f` be the universal morphism from `F.obj U` to the equalizer
    -- of the sheaf condition fork, whatever it is.
    -- Our goal is to show that this is an isomorphism.
    let f := equalizer.lift _ (w F U),
    -- If we can do that,
    suffices : is_iso (G.map f),
    { resetI,
      -- we have that `f` itself is an isomorphism, since `G` reflects isomorphisms
      haveI : is_iso f := is_iso_of_reflects_iso f G,
      -- TODO package this up as a result elsewhere:
      apply is_limit.of_iso_limit (limit.is_limit _),
      apply iso.symm,
      fapply cones.ext,
      exact (as_iso f),
      rintro ⟨_|_⟩; { dsimp [f], simp, }, },
    { -- Returning to the task of shwoing that `G.map f` is an isomorphism,
      -- we note that `G.map f` is almost but not quite (see below) a morphism
      -- from the sheaf condition cone for `F ⋙ G` to the
      -- image under `G` of the equalizer cone for the sheaf condition diagram.
      let c := fork (F ⋙ G) U,
      obtain ⟨hc⟩ := S U,
      let d := G.map_cone (equalizer.fork (left_res F U) (right_res F U)),
      have hd : is_limit d := preserves_limit.preserves (limit.is_limit _),
      -- Since both of these are limit cones
      -- (`c` by our hypothesis `S`, and `d` because `G` preserves limits),
      -- we hope to be able to conclude that `f` is an isomorphism.
      -- We say "not quite" above because `c` and `d` don't quite have the same shape:
      -- we need to postcompose by the natural isomorphism `diagram_comp_preserves_limits`
      -- introduced above.
      let d' := (cones.postcompose (diagram_comp_preserves_limits G F U).hom).obj d,
      have hd' : is_limit d' :=
        (is_limit.postcompose_hom_equiv (diagram_comp_preserves_limits G F U) d).symm hd,
      -- Now everything works: we verify that `f` really is a morphism between these cones:
      let f' : c ⟶ d' :=
      fork.mk_hom (G.map f)
      begin
        dsimp only [c, d, d', f, diagram_comp_preserves_limits, res],
        dunfold fork.ι,
        ext1 j,
        dsimp,
        simp only [category.assoc, ←functor.map_comp_assoc, equalizer.lift_ι,
          map_lift_pi_comparison_assoc],
        dsimp [res], simp,
      end,
      -- conclude that it is an isomorphism,
      -- just because it's a morphism between two limit cones.
      haveI : is_iso f' := is_limit.hom_is_iso hc hd' f',
      -- A cone morphism is an isomorphism exactly if the morphism between the cone points is,
      -- so we're done!
      exact is_iso.of_iso ((cones.forget _).map_iso (as_iso f')) }, },
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

end presheaf

end Top
