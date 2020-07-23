import topology.sheaves.sheaf
import category_theory.limits.preserves.shapes
import category_theory.limits.types

/-!
# Checking the sheaf condition on the underlying presheaf of types.

When `C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphism,
the sheaf condition on a `C`-valued presheaf is equivalent to
the sheaf condition on the underlying `Type`-valued presheaf.

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
local attribute [reducible] sheaf_condition.left_restriction sheaf_condition.right_restriction

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
  { ext, simp, dsimp, simp, }, -- `squeeze_simp` produces invalid output
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

local attribute [reducible] sheaf_condition.restriction

def map_cone_fork : G.map_cone (sheaf_condition.fork F U) ≅
  (cones.postcompose (diagram_comp_preserves_limits G F U).inv).obj (sheaf_condition.fork (F ⋙ G) U) :=
cones.ext (iso.refl _) (λ j,
begin
  dsimp, simp [diagram_comp_preserves_limits], cases j; dsimp,
  { rw iso.eq_comp_inv,
    ext,
    simp, dsimp, simp, },
  { rw iso.eq_comp_inv,
    ext,
    simp, -- squeeze_simp fails
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

-- TODO I'd prefer this isn't necessary
local attribute [-simp] forget_map_eq_coe

/--
If `C` is a concrete category with a forgetful functor that preserves limits and reflects isomorphisms,
to check the sheaf condition it suffices to check it on the underlying sheaf of types.
-/
def sheaf_condition_equiv_sheaf_condition_forget :
  sheaf_condition F ≃ sheaf_condition (F ⋙ (forget C)) :=
begin
  fsplit,
  { intros S ι U,
    have t1 := S U,
    have t2 := @preserves_limit.preserves _ _ _ _ _ _ _ (forget C) _ _ t1,
    have t3 := is_limit.of_iso_limit t2 (map_cone_fork _ _ _),
    have t4 := is_limit.postcompose_inv_equiv _ _ t3,
    exact t4, },
  { intros S ι U,
    let f := equalizer.lift _ (fork_condition F U),
    haveI : is_iso ((forget C).map f) :=
    begin
      let c := sheaf_condition.fork (F ⋙ forget C) U,
      have hc : is_limit c := S U,
      let d := (forget C).map_cone (equalizer.fork (left_restriction F U) (right_restriction F U)),
      have hd : is_limit d := preserves_limit.preserves (limit.is_limit _),
      -- `c` is a limit cone by `S`
      -- `d` is a limit cone because `forget C` preserves limits
      -- `(forget C).map f` is a morphism from `c` to `d`
      -- so it's an isomorphism...
      -- EXCEPT: `c` and `d` don't quite have the same shape yet.
      let d' := (cones.postcompose (diagram_comp_preserves_limits _ F U).hom).obj d,
      have hd' : is_limit d' := (is_limit.postcompose_hom_equiv.{u} (diagram_comp_preserves_limits (forget C) F U) _).symm hd,
      let g : c ⟶ d' :=
      fork.mk_hom ((forget C).map f)
      begin
        dsimp only [c, d, d', f, diagram_comp_preserves_limits, restriction],
        dunfold fork.ι,
        ext1 j,
        dsimp,
        simp only [category.assoc],
        simp only [←functor.map_comp_assoc],
        simp only [equalizer.lift_ι, lift_comp_preserves_products_iso_hom_assoc],
        dsimp [restriction], simp,
      end,
      haveI : is_iso g := is_limit.hom_is_iso hc hd' g,
      exact { ..((cones.forget _).map_iso (as_iso g)) },
    end,
    haveI : is_iso f := is_iso_of_reflects_iso f (forget C),
    apply is_limit.of_iso_limit (limit.is_limit _),
    apply iso.symm,
    fapply cones.ext,
    exact (as_iso f),
    rintro ⟨_|_⟩; { dsimp [f], simp, }, },
  { intros S, apply subsingleton.elim, },
  { intros S, apply subsingleton.elim, },
end

end Top
