/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.limits.kan_extension

/-!
# Cocontinuous functors between sites.

We define cocontinuous functors between sites as functors that pull covering sieves back to
covering sieves. This seems stronger than the definition found in stacks project,
but they are actually equivalent via `category_theory.grothendieck_topology.superset_covering`.
(The precise statement is not formalized, but follows from it quite trivially).

This concept is also called the "covering lifting property" as defined in [MM92] Chapter VII,
Section 10, and should not be confused with the general definition of cocontinuous functors
between categories as functors preserving small colimits.

## Main Results
- `category_theory.sites.Ran_is_sheaf_of_cocontinuous`: If `u : C ⥤ D` is cocontinuous, then
`Ran u.op` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/

universes u
noncomputable theory

open category_theory
open opposite
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.limits

namespace category_theory
namespace sites
variables {C D A : Type u} [category.{u} C] [category.{u} D] [category.{u} A] [has_limits A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}

/--
A functor `u : (C, J) ⥤ (D, K)` between sites is called cocontinuous if for all covering sieves
`R` in `D`, `R.pullback u` is a covering sieve in `C`.
-/
structure cocontinuous (J : grothendieck_topology C) (K : grothendieck_topology D) (u : C ⥤ D) :=
(cover_lift : ∀ {U : C} {S : sieve (u.obj U)} (hS : S ∈ K (u.obj U)), S.functor_pullback u ∈ J U)

/-- A trivial example to make the inhabited linter happy. -/
instance id_cocontinuous : inhabited (cocontinuous J J (𝟭 _)) :=
⟨⟨λ _ S h, by { convert h, simp }⟩⟩

/-!
We will now prove that `Ran u.op` (`ₚu`) maps sheaves to sheaves if `u` is cocontinuous. This can
be found in https://stacks.math.columbia.edu/tag/00XK. However, the proof given here uses the
amalgamation definition of sheaves, and thus does not require that `C` or `D` has categorical
pullbacks.

For the following proof sketch, `⊆` denotes the homs on `C` and `D` as in the topological analogy.
By definition, the presheaf `𝒢 : Dᵒᵖ ⥤ A` is a sheaf if for every sieve `S` of `U : D`, and every
compatible family of morphisms `X ⟶ 𝒢(V)` for each `V ⊆ U : S` with a fixed source `X`,
we can glue them into a morphism `X ⟶ 𝒢(U)`.

Since the presheaf `𝒢 := (Ran u.op).obj ℱ.val` is defined via `𝒢(U) = lim_{u(V) ⊆ U} ℱ(V)`, for
gluing the family `x` into a `X ⟶ 𝒢(U)`, it suffices to provide a `X ⟶ ℱ(Y)` for each
`u(Y) ⊆ U`. This can be done since `{ Y' ⊆ Y : u(Y') ⊆ U ∈ S}` is a covering sieve for `Y` on
`C` (by the cocontinuity of `u`). Thus the morphisms `X ⟶ 𝒢(u(Y')) ⟶ ℱ(Y')` can be glued into
a morphism `X ⟶ ℱ(Y)`. This is done in `get_sections`.

In `glued_limit_cone`, we verify these obtained sections are indeed compatible, and thus we obtain
A `X ⟶ 𝒢(U)`. The remaining work is to verify that this is indeed the amalgamation and is unique.
-/
namespace Ran_is_sheaf_of_cocontinuous
variables {u : C ⥤ D} (hu : cocontinuous J K u) (ℱ : Sheaf J A)
variables {X : A} {U : D} (S : sieve U) (hS : S ∈ K U)
variables (x : S.arrows.family_of_elements ((Ran u.op).obj ℱ.val ⋙ coyoneda.obj (op X)))
variables (hx : x.compatible)

/-- The family of morphisms `X ⟶ 𝒢(u(Y')) ⟶ ℱ(Y')` defined on `{ Y' ⊆ Y : u(Y') ⊆ U ∈ S}`. -/
@[reducible] def pullbacked_family (Y : structured_arrow (op U) u.op) :=
(((x.pullback Y.3.unop).functor_pullback u).comp_presheaf_map
  (show _ ⟶ _, from whisker_right ((Ran.adjunction A u.op).counit.app ℱ.val)
    (coyoneda.obj (op X))))

@[simp] lemma pullbacked_family_apply (Y : structured_arrow (op U) u.op) {W} {f : W ⟶ _} (Hf) :
  pullbacked_family ℱ S x Y f Hf =
    x (u.map f ≫ Y.hom.unop) Hf ≫ ((Ran.adjunction A u.op).counit.app ℱ.val).app (op W) := rfl

variables {x} {S}
include hu hS hx

/-- Given a `u(Y) ⊆ U`, we can find a unique section `X ⟶ ℱ(Y)` that agrees with `x`. -/
lemma get_section (Y : structured_arrow (op U) u.op) :
 ∃! t, (pullbacked_family ℱ S x Y).is_amalgamation t :=
begin
  let hom_sh := whisker_right ((Ran.adjunction A u.op).counit.app ℱ.val) (coyoneda.obj (op X)),
  have S' := (K.pullback_stable Y.hom.unop hS),
  have hs' := ((hx.pullback Y.3.unop).functor_pullback u).comp_presheaf_map hom_sh,
  exact ℱ.2 X _ (hu.cover_lift S') _ hs',
end

/-- The limit cone in order to glue the sections obtained via `get_section`. -/
@[reducible] def glued_limit_cone : limits.cone (Ran.diagram u.op ℱ.val (op U)) :=
{ X := X, π :=
  { app := λ Y, classical.some (get_section hu ℱ hS hx Y),
    naturality' := λ Y Z f, by
    { simp only [functor.comp_map, structured_arrow.proj_map, functor.const.obj_map],
      erw category.id_comp,
      obtain ⟨Pt₁, _⟩ := classical.some_spec (get_section hu ℱ hS hx Y),
      generalize ht₁ : classical.some (get_section hu ℱ hS hx Y) = t₁,
      rw ht₁ at Pt₁,
      apply unique_of_exists_unique
          (get_section hu ℱ hS hx Z) (classical.some_spec (get_section hu ℱ hS hx Z)).1,
      intros W fw hw,
      have eq := congr_arg quiver.hom.unop f.w,
      erw category.id_comp at eq,
      convert Pt₁ (fw ≫ f.right.unop) (by {
        change S (u.map _ ≫ Y.hom.unop),
        rw eq at hw,
        simpa using hw,
      }) using 1,
      { tidy },
      { simp[eq] } } } }

/-- The section obtained by passing `glued_limit_cone` into `category_theory.limits.limit.lift`. -/
@[reducible] def glued_section : X ⟶ ((Ran u.op).obj ℱ.val).obj (op U) :=
limit.lift _ (glued_limit_cone hu ℱ hS hx)

/--
A helper lemma for the following two lemmas. Basically stating that if the section `y : X ⟶ 𝒢(V)`
coincides with `x` on `u(V')` for all `u(V') ⊆ V ∈ S`, then `X ⟶ 𝒢(V) ⟶ ℱ(W)` is indeed the
section obtained in `get_sections`. That said, this is littered with some more categorical jargon
in order to be applied in the following lemmas easier.
-/
lemma helper {V} (f : V ⟶ U) (y : X ⟶ ((Ran u.op).obj ℱ.val).obj (op V)) (W)
  (H : ∀ {V'} {fV : u.obj V' ⟶ V} (hV), y ≫ ((Ran u.op).obj ℱ.val).map fV.op = x (fV ≫ f) hV) :
  y ≫ limit.π (Ran.diagram u.op ℱ.val (op V)) W =
    (glued_limit_cone hu ℱ hS hx).π.app ((structured_arrow.map f.op).obj W) :=
begin
  apply unique_of_exists_unique
    (get_section hu ℱ hS hx ((structured_arrow.map f.op).obj W)) _
    (classical.some_spec (get_section hu ℱ hS hx ((structured_arrow.map f.op).obj W))).1,
  intros V' fV' hV',
  dsimp only [Ran.adjunction, Ran.equiv, pullbacked_family_apply],
  delta structured_arrow.map comma.map_left at hV' ⊢,
  change S _ at hV',
  simp only [quiver.hom.unop_op, functor.const.map_app, unop_comp, ← category.assoc] at hV' ⊢,
  erw ← H hV',
  simp only [adjunction.adjunction_of_equiv_right_counit_app,
    Ran_obj_map, quiver.hom.op_unop, equiv.symm_symm, equiv.coe_fn_mk,
    whisker_right_app, functor.comp_map, coyoneda_obj_map, category.assoc],
  erw category.id_comp,
  erw limit.pre_π,
  congr,
  convert limit.w (Ran.diagram u.op ℱ.val (op V)) (structured_arrow.hom_mk' W fV'.op),
  rw structured_arrow.map_mk,
  erw category.comp_id,
  simp
end

/-- Verify that the `glued_section` is an amalgamation of `x`. -/
lemma glued_section_is_amalgamation : x.is_amalgamation (glued_section hu ℱ hS hx) :=
begin
  intros V fV hV,
  ext W,
  simp only [functor.comp_map, limit.lift_pre, coyoneda_obj_map, Ran_obj_map, glued_section],
  erw limit.lift_π,
  symmetry,
  convert helper hu ℱ hS hx _ (x fV hV) _ _,
  intros V' fV' hV',
  convert hx (fV') (𝟙 _) hV hV' (by simp),
  simp
end

/-- Verify that the amalgamation is indeed unique. -/
lemma glued_section_is_unique (y) (hy: x.is_amalgamation y) : y = glued_section hu ℱ hS hx :=
begin
  unfold glued_section limit.lift,
  ext W,
  erw limit.lift_π,
  convert helper hu ℱ hS hx (𝟙 _) y W _,
  { apply unique_of_exists_unique (get_section hu ℱ hS hx W),
    exact (classical.some_spec (get_section hu ℱ hS hx W)).1,
    convert (classical.some_spec (get_section hu ℱ hS hx ((structured_arrow.map (𝟙 _)).obj W))).1;
    erw structured_arrow.map_id },
  { intros V' fV' hV',
    convert hy fV' (by simpa using hV'),
    erw category.comp_id }
end

end Ran_is_sheaf_of_cocontinuous

/--
If `u` is cocontinuous, then `Ran u.op` pushes sheaves to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00XK,
but without the condition that `C` or `D` has pullbacks.
-/
theorem Ran_is_sheaf_of_cocontinuous {u : C ⥤ D} (hu : cocontinuous J K u) (ℱ : Sheaf J A) :
  presheaf.is_sheaf K ((Ran u.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  split, swap,
  { apply Ran_is_sheaf_of_cocontinuous.glued_section hu ℱ hS hx },
  split,
  { apply Ran_is_sheaf_of_cocontinuous.glued_section_is_amalgamation },
  { apply Ran_is_sheaf_of_cocontinuous.glued_section_is_unique }
end

end sites
end category_theory
