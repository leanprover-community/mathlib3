/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.limits.kan_extension

/-!
# Cover-lifting functors between sites.

We define cover-lifting functors between sites as functors that pull covering sieves back to
covering sieves. This concept is also known as *cocontinuous functors* or
*cover-reflecting functors*, but we have chosen this name following [MM92] in order to avoid
potential naming collision or confusion with the general definition of cocontinuous functors
between categories as functors preserving small colimits.

The definition given here seems stronger than the definition found elsewhere,
but they are actually equivalent via `category_theory.grothendieck_topology.superset_covering`.
(The precise statement is not formalized, but follows from it quite trivially).

## Main definitions

* `category_theory.sites.cover_lifting`: a functor between sites is cover_lifting if it
pulls back covering sieves to covering sieves

## Main results
- `category_theory.sites.Ran_is_sheaf_of_cover_lifting`: If `G : C ⥤ D` is cover_lifting, then
`Ran G.op` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/

universes v u
noncomputable theory

open category_theory
open opposite
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.limits

namespace category_theory
section cover_lifting
variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {L : grothendieck_topology E}

/--
A functor `G : (C, J) ⥤ (D, K)` between sites is called to have the cover-lifting property
if for all covering sieves `R` in `D`, `R.pullback G` is a covering sieve in `C`.
-/
@[nolint has_inhabited_instance]
structure cover_lifting (J : grothendieck_topology C) (K : grothendieck_topology D) (G : C ⥤ D) :=
(cover_lift : ∀ {U : C} {S : sieve (G.obj U)} (hS : S ∈ K (G.obj U)), S.functor_pullback G ∈ J U)

/-- The identity functor on a site is cover-lifting. -/
def id_cover_lifting : cover_lifting J J (𝟭 _) := ⟨λ _ _ h, by simpa using h⟩

/-- The composition of two cover-lifting functors are cover-lifting -/
def comp_cover_lifting {G} (hu : cover_lifting J K G) {v} (hv : cover_lifting K L v) :
  cover_lifting J L (G ⋙ v) := ⟨λ _ S h, hu.cover_lift (hv.cover_lift h)⟩

end cover_lifting

/-!
We will now prove that `Ran G.op` (`ₚu`) maps sheaves to sheaves if `G` is cover-lifting. This can
be found in https://stacks.math.columbia.edu/tag/00XK. However, the proof given here uses the
amalgamation definition of sheaves, and thus does not require that `C` or `D` has categorical
pullbacks.

For the following proof sketch, `⊆` denotes the homs on `C` and `D` as in the topological analogy.
By definition, the presheaf `𝒢 : Dᵒᵖ ⥤ A` is a sheaf if for every sieve `S` of `U : D`, and every
compatible family of morphisms `X ⟶ 𝒢(V)` for each `V ⊆ U : S` with a fixed source `X`,
we can glue them into a morphism `X ⟶ 𝒢(U)`.

Since the presheaf `𝒢 := (Ran G.op).obj ℱ.val` is defined via `𝒢(U) = lim_{G(V) ⊆ U} ℱ(V)`, for
gluing the family `x` into a `X ⟶ 𝒢(U)`, it suffices to provide a `X ⟶ ℱ(Y)` for each
`G(Y) ⊆ U`. This can be done since `{ Y' ⊆ Y : G(Y') ⊆ U ∈ S}` is a covering sieve for `Y` on
`C` (by the cover-lifting property of `G`). Thus the morphisms `X ⟶ 𝒢(G(Y')) ⟶ ℱ(Y')` can be
glued into a morphism `X ⟶ ℱ(Y)`. This is done in `get_sections`.

In `glued_limit_cone`, we verify these obtained sections are indeed compatible, and thus we obtain
A `X ⟶ 𝒢(U)`. The remaining work is to verify that this is indeed the amalgamation and is unique.
-/
variables {C D : Type u} [category.{u} C] [category.{u} D]
variables {A : Type v} [category.{u} A] [has_limits A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}

namespace Ran_is_sheaf_of_cover_lifting
variables {G : C ⥤ D} (hu : cover_lifting J K G) (ℱ : Sheaf J A)
variables {X : A} {U : D} (S : sieve U) (hS : S ∈ K U)
variables (x : S.arrows.family_of_elements ((Ran G.op).obj ℱ.val ⋙ coyoneda.obj (op X)))
variables (hx : x.compatible)

/-- The family of morphisms `X ⟶ 𝒢(G(Y')) ⟶ ℱ(Y')` defined on `{ Y' ⊆ Y : G(Y') ⊆ U ∈ S}`. -/
def pulledback_family (Y : structured_arrow (op U) G.op) :=
(((x.pullback Y.hom.unop).functor_pullback G).comp_presheaf_map
  (show _ ⟶ _, from whisker_right ((Ran.adjunction A G.op).counit.app ℱ.val)
    (coyoneda.obj (op X))))

@[simp] lemma pulledback_family_apply (Y : structured_arrow (op U) G.op) {W} {f : W ⟶ _} (Hf) :
  pulledback_family ℱ S x Y f Hf =
    x (G.map f ≫ Y.hom.unop) Hf ≫ ((Ran.adjunction A G.op).counit.app ℱ.val).app (op W) := rfl

variables {x} {S}
include hu hS hx

/-- Given a `G(Y) ⊆ U`, we can find a unique section `X ⟶ ℱ(Y)` that agrees with `x`. -/
def get_section (Y : structured_arrow (op U) G.op) : X ⟶ ℱ.val.obj Y.right :=
begin
  let hom_sh := whisker_right ((Ran.adjunction A G.op).counit.app ℱ.val) (coyoneda.obj (op X)),
  have S' := (K.pullback_stable Y.hom.unop hS),
  have hs' := ((hx.pullback Y.3.unop).functor_pullback G).comp_presheaf_map hom_sh,
  exact (ℱ.2 X _ (hu.cover_lift S')).amalgamate _ hs'
end

lemma get_section_is_amalgamation (Y : structured_arrow (op U) G.op) :
  (pulledback_family ℱ S x Y).is_amalgamation (get_section hu ℱ hS hx Y) :=
is_sheaf_for.is_amalgamation _ _

lemma get_section_is_unique (Y : structured_arrow (op U) G.op)
  {y} (H : (pulledback_family ℱ S x Y).is_amalgamation y) : y = get_section hu ℱ hS hx Y :=
begin
  apply is_sheaf_for.is_separated_for _ (pulledback_family ℱ S x Y),
  { exact H },
  { apply get_section_is_amalgamation },
  { exact ℱ.2 X _ (hu.cover_lift (K.pullback_stable Y.hom.unop hS)) }
end

@[simp] lemma get_section_commute {Y Z : structured_arrow (op U) G.op} (f : Y ⟶ Z) :
  get_section hu ℱ hS hx Y ≫ ℱ.val.map f.right = get_section hu ℱ hS hx Z :=
begin
  apply get_section_is_unique,
  intros V' fV' hV',
  have eq : Z.hom = Y.hom ≫ (G.map f.right.unop).op,
  { convert f.w, erw category.id_comp },
  rw eq at hV',
  convert get_section_is_amalgamation hu ℱ hS hx Y (fV' ≫ f.right.unop) _ using 1,
  { tidy },
  { simp only [eq, quiver.hom.unop_op, pulledback_family_apply,
    functor.map_comp, unop_comp, category.assoc] },
  { change S (G.map _ ≫ Y.hom.unop),
    simpa only [functor.map_comp, category.assoc] using hV' }
end

/-- The limit cone in order to glue the sections obtained via `get_section`. -/
def glued_limit_cone : limits.cone (Ran.diagram G.op ℱ.val (op U)) :=
{ X := X, π := { app := λ Y, get_section hu ℱ hS hx Y, naturality' := λ Y Z f, by tidy } }

@[simp] lemma glued_limit_cone_π_app (W) : (glued_limit_cone hu ℱ hS hx).π.app W =
  get_section hu ℱ hS hx W := rfl

/-- The section obtained by passing `glued_limit_cone` into `category_theory.limits.limit.lift`. -/
def glued_section : X ⟶ ((Ran G.op).obj ℱ.val).obj (op U) :=
limit.lift _ (glued_limit_cone hu ℱ hS hx)

/--
A helper lemma for the following two lemmas. Basically stating that if the section `y : X ⟶ 𝒢(V)`
coincides with `x` on `G(V')` for all `G(V') ⊆ V ∈ S`, then `X ⟶ 𝒢(V) ⟶ ℱ(W)` is indeed the
section obtained in `get_sections`. That said, this is littered with some more categorical jargon
in order to be applied in the following lemmas easier.
-/
lemma helper {V} (f : V ⟶ U) (y : X ⟶ ((Ran G.op).obj ℱ.val).obj (op V)) (W)
  (H : ∀ {V'} {fV : G.obj V' ⟶ V} (hV), y ≫ ((Ran G.op).obj ℱ.val).map fV.op = x (fV ≫ f) hV) :
  y ≫ limit.π (Ran.diagram G.op ℱ.val (op V)) W =
    (glued_limit_cone hu ℱ hS hx).π.app ((structured_arrow.map f.op).obj W) :=
begin
  dsimp only [glued_limit_cone_π_app],
  apply get_section_is_unique hu ℱ hS hx ((structured_arrow.map f.op).obj W),
  intros V' fV' hV',
  dsimp only [Ran.adjunction, Ran.equiv, pulledback_family_apply],
  erw [adjunction.adjunction_of_equiv_right_counit_app],
  have : y ≫ ((Ran G.op).obj ℱ.val).map (G.map fV' ≫ W.hom.unop).op =
    x (G.map fV' ≫ W.hom.unop ≫ f) (by simpa only using hV'),
  { convert H (show S ((G.map fV' ≫ W.hom.unop) ≫ f),
      by simpa only [category.assoc] using hV') using 2,
    simp only [category.assoc] },
  simp only [quiver.hom.unop_op, equiv.symm_symm, structured_arrow.map_obj_hom, unop_comp,
    equiv.coe_fn_mk, functor.comp_map, coyoneda_obj_map, category.assoc, ← this, op_comp,
    Ran_obj_map, nat_trans.id_app],
  erw [category.id_comp, limit.pre_π],
  congr,
  convert limit.w (Ran.diagram G.op ℱ.val (op V)) (structured_arrow.hom_mk' W fV'.op),
  rw structured_arrow.map_mk,
  erw category.comp_id,
  simp only [quiver.hom.unop_op, functor.op_map, quiver.hom.op_unop]
end

/-- Verify that the `glued_section` is an amalgamation of `x`. -/
lemma glued_section_is_amalgamation : x.is_amalgamation (glued_section hu ℱ hS hx) :=
begin
  intros V fV hV,
  ext W,
  simp only [functor.comp_map, limit.lift_pre, coyoneda_obj_map, Ran_obj_map, glued_section],
  erw limit.lift_π,
  symmetry,
  convert helper hu ℱ hS hx _ (x fV hV) _ _ using 1,
  intros V' fV' hV',
  convert hx (fV') (𝟙 _) hV hV' (by rw category.id_comp),
  simp only [op_id, functor_to_types.map_id_apply]
end

/-- Verify that the amalgamation is indeed unique. -/
lemma glued_section_is_unique (y) (hy: x.is_amalgamation y) : y = glued_section hu ℱ hS hx :=
begin
  unfold glued_section limit.lift,
  ext W,
  erw limit.lift_π,
  convert helper hu ℱ hS hx (𝟙 _) y W _,
  { simp only [op_id, structured_arrow.map_id] },
  { intros V' fV' hV',
    convert hy fV' (by simpa only [category.comp_id] using hV'),
    erw category.comp_id }
end

end Ran_is_sheaf_of_cover_lifting

/--
If `G` is cover_lifting, then `Ran G.op` pushes sheaves to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00XK,
but without the condition that `C` or `D` has pullbacks.
-/
theorem Ran_is_sheaf_of_cover_lifting {G : C ⥤ D} (hu : cover_lifting J K G) (ℱ : Sheaf J A) :
  presheaf.is_sheaf K ((Ran G.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  split, swap,
  { apply Ran_is_sheaf_of_cover_lifting.glued_section hu ℱ hS hx },
  split,
  { apply Ran_is_sheaf_of_cover_lifting.glued_section_is_amalgamation },
  { apply Ran_is_sheaf_of_cover_lifting.glued_section_is_unique }
end

end category_theory
