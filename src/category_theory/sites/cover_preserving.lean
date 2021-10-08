/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.limits.kan_extension
import category_theory.flat_functors

/-!
# Cover-lifting functors between sites.

We define cover-lifting functors between sites as functors that pull covering sieves back to
covering sieves. This concept is also known as *cocontinuous functors*, but we have chosen this
name following [Elephant] in order to avoid naming collision or confusion with the general
definition of cover_lifting functors between categories as functors preserving small colimits.

The definition given here seems stronger than the definition found elsewhere,
but they are actually equivalent via `category_theory.grothendieck_topology.superset_covering`.
(The precise statement is not formalized, but follows from it quite trivially).

## Main definitions

* `category_theory.sites.cover_lifting`: a functor between sites is cover_lifting if it
pulls back covering sieves to covering sieves

## Main results
- `category_theory.sites.Ran_is_sheaf_of_cover_lifting`: If `u : C ⥤ D` is cover_lifting, then
`Ran u.op` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/

universes v
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
A functor `u : (C, J) ⥤ (D, K)` between sites is called to have the cover-lifting property
if for all covering sieves `R` in `D`, `R.pullback u` is a covering sieve in `C`.
-/
@[nolint has_inhabited_instance]
structure cover_preserving (J : grothendieck_topology C) (K : grothendieck_topology D) (u : C ⥤ D) :=
(cover_preserve : ∀ {U : C} {S : sieve U} (hS : S ∈ J U), S.functor_pushforward u ∈ K (u.obj U))

-- set_option pp.universes true

lemma compatible.functor_pushforward {C : Type*} {D : Type*} [category.{v} C] [category.{v} D]
  {u : C ⥤ D} [representably_flat u] {P : Dᵒᵖ ⥤ Type _} {Z : C} {T : presieve Z}
  {x : family_of_elements (u.op ⋙ P) T} (h : x.compatible) :
  (family_of_elements.functor_pushforward u x).compatible :=
begin
  intros Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq,
  have := λ x, h x,
  let K := cospan (functor_pushforward_prehom h₁) (functor_pushforward_prehom h₂),
  have : cospan f₁ f₂ = K ⋙ u, admit,
  -- { fapply functor.ext,
  --   { intro X, cases X, simp, cases X; simp },
  --   { intros X Y f, cases f, cases X; simpa, cases f_1; simpa } },
  let c := (cones.postcompose (eq_to_hom this)).obj (pullback_cone.mk g₁ g₂ eq),
  -- let c : cone (K ⋙ u) :=
  --   { X := W,
  --     π := {
  --       app := λ j, by { cases j, exact g₁ ≫ f₁, cases j,
  --         exact g₁ ≫ (eq_to_hom (by simp)) ,exact g₂ ≫ (eq_to_hom (by simp)) },
  --       naturality' := λ j k f, by
  --         { cases f,
  --           cases j,
  --           simp[@category.comp_id _ _ _ (u.obj (K.obj none)), @category.id_comp _ _ W],
  --           cases j, simp,   } }
  -- },
  -- let X₀ := structured_arrow.mk
  -- let f₁' := structured_arrow.mk (u.map (functor_pushforward_prehom h₁)),
  -- let f₂' := structured_arrow.mk (u.map (functor_pushforward_prehom h₂)),
  -- haveI : is_cofiltered (costructured_arrow u (u.obj Z)) := u.flat_cofiltered _,
  have := h (is_cofiltered.min f₁' f₂').left (u.flat_min_right f₁' f₂').left
    (functor_pushforward_prehom_cover h₁) (functor_pushforward_prehom_cover h₂) (by {
      have := (u.flat_min f₁' f₂').hom, simp at this,
    })
end


-- /-- The identity functor on a site is cover-lifting. -/
-- def id_cover_lifting : cover_lifting J J (𝟭 _) := ⟨λ _ _ h, by simpa using h⟩

-- /-- The composition of two cover-lifting functors are cover-lifting -/
-- def comp_cover_lifting {u} (hu : cover_lifting J K u) {v} (hv : cover_lifting K L v) :
--   cover_lifting J L (u ⋙ v) := ⟨λ _ S h, hu.cover_lift (hv.cover_lift h)⟩

end cover_lifting

/-!
We will now prove that `Ran u.op` (`ₚu`) maps sheaves to sheaves if `u` is cover-lifting. This can
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
`C` (by the cover-lifting property of `u`). Thus the morphisms `X ⟶ 𝒢(u(Y')) ⟶ ℱ(Y')` can be
glued into a morphism `X ⟶ ℱ(Y)`. This is done in `get_sections`.

In `glued_limit_cone`, we verify these obtained sections are indeed compatible, and thus we obtain
A `X ⟶ 𝒢(U)`. The remaining work is to verify that this is indeed the amalgamation and is unique.
-/
variables {C D : Type u} [category.{u} C] [category.{u} D]
variables {A : Type v} [category.{u} A] [has_limits A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}

-- namespace Ran_is_sheaf_of_cover_lifting
-- variables {u : C ⥤ D} (hu : cover_lifting J K u) (ℱ : Sheaf J A)
-- variables {X : A} {U : D} (S : sieve U) (hS : S ∈ K U)
-- variables (x : S.arrows.family_of_elements ((Ran u.op).obj ℱ.val ⋙ coyoneda.obj (op X)))
-- variables (hx : x.compatible)

-- /-- The family of morphisms `X ⟶ 𝒢(u(Y')) ⟶ ℱ(Y')` defined on `{ Y' ⊆ Y : u(Y') ⊆ U ∈ S}`. -/
-- def pulledback_family (Y : structured_arrow (op U) u.op) :=
-- (((x.pullback Y.hom.unop).functor_pullback u).comp_presheaf_map
--   (show _ ⟶ _, from whisker_right ((Ran.adjunction A u.op).counit.app ℱ.val)
--     (coyoneda.obj (op X))))

-- @[simp] lemma pulledback_family_apply (Y : structured_arrow (op U) u.op) {W} {f : W ⟶ _} (Hf) :
--   pulledback_family ℱ S x Y f Hf =
--     x (u.map f ≫ Y.hom.unop) Hf ≫ ((Ran.adjunction A u.op).counit.app ℱ.val).app (op W) := rfl

-- variables {x} {S}
-- include hu hS hx

-- /-- Given a `u(Y) ⊆ U`, we can find a unique section `X ⟶ ℱ(Y)` that agrees with `x`. -/
-- def get_section (Y : structured_arrow (op U) u.op) : X ⟶ ℱ.val.obj Y.right :=
-- begin
--   let hom_sh := whisker_right ((Ran.adjunction A u.op).counit.app ℱ.val) (coyoneda.obj (op X)),
--   have S' := (K.pullback_stable Y.hom.unop hS),
--   have hs' := ((hx.pullback Y.3.unop).functor_pullback u).comp_presheaf_map hom_sh,
--   exact (ℱ.2 X _ (hu.cover_lift S')).amalgamate _ hs'
-- end

-- lemma get_section_is_amalgamation (Y : structured_arrow (op U) u.op) :
--   (pulledback_family ℱ S x Y).is_amalgamation (get_section hu ℱ hS hx Y) :=
-- is_sheaf_for.is_amalgamation _ _

-- lemma get_section_is_unique (Y : structured_arrow (op U) u.op)
--   {y} (H : (pulledback_family ℱ S x Y).is_amalgamation y) : y = get_section hu ℱ hS hx Y :=
-- begin
--   apply is_sheaf_for.is_separated_for _ (pulledback_family ℱ S x Y),
--   { exact H },
--   { apply get_section_is_amalgamation },
--   { exact ℱ.2 X _ (hu.cover_lift (K.pullback_stable Y.hom.unop hS)) }
-- end

-- @[simp] lemma get_section_commute {Y Z : structured_arrow (op U) u.op} (f : Y ⟶ Z) :
--   get_section hu ℱ hS hx Y ≫ ℱ.val.map f.right = get_section hu ℱ hS hx Z :=
-- begin
--   apply get_section_is_unique,
--   intros V' fV' hV',
--   have eq : Z.hom = Y.hom ≫ (u.map f.right.unop).op,
--   { convert f.w, erw category.id_comp },
--   rw eq at hV',
--   convert get_section_is_amalgamation hu ℱ hS hx Y (fV' ≫ f.right.unop) _ using 1,
--   { tidy },
--   { simp [eq] },
--   { change S (u.map _ ≫ Y.hom.unop),
--     simpa using hV' }
-- end

-- /-- The limit cone in order to glue the sections obtained via `get_section`. -/
-- def glued_limit_cone : limits.cone (Ran.diagram u.op ℱ.val (op U)) :=
-- { X := X, π := { app := λ Y, get_section hu ℱ hS hx Y, naturality' := λ Y Z f, by tidy } }

-- @[simp] lemma glued_limit_cone_π_app (W) : (glued_limit_cone hu ℱ hS hx).π.app W =
--   get_section hu ℱ hS hx W := rfl

-- /-- The section obtained by passing `glued_limit_cone` into `category_theory.limits.limit.lift`. -/
-- def glued_section : X ⟶ ((Ran u.op).obj ℱ.val).obj (op U) :=
-- limit.lift _ (glued_limit_cone hu ℱ hS hx)

-- /--
-- A helper lemma for the following two lemmas. Basically stating that if the section `y : X ⟶ 𝒢(V)`
-- coincides with `x` on `u(V')` for all `u(V') ⊆ V ∈ S`, then `X ⟶ 𝒢(V) ⟶ ℱ(W)` is indeed the
-- section obtained in `get_sections`. That said, this is littered with some more categorical jargon
-- in order to be applied in the following lemmas easier.
-- -/
-- lemma helper {V} (f : V ⟶ U) (y : X ⟶ ((Ran u.op).obj ℱ.val).obj (op V)) (W)
--   (H : ∀ {V'} {fV : u.obj V' ⟶ V} (hV), y ≫ ((Ran u.op).obj ℱ.val).map fV.op = x (fV ≫ f) hV) :
--   y ≫ limit.π (Ran.diagram u.op ℱ.val (op V)) W =
--     (glued_limit_cone hu ℱ hS hx).π.app ((structured_arrow.map f.op).obj W) :=
-- begin
--   dsimp only [glued_limit_cone_π_app],
--   apply get_section_is_unique hu ℱ hS hx ((structured_arrow.map f.op).obj W),
--   intros V' fV' hV',
--   dsimp only [Ran.adjunction, Ran.equiv, pulledback_family_apply],
--   erw [adjunction.adjunction_of_equiv_right_counit_app],
--   have : y ≫ ((Ran u.op).obj ℱ.val).map (u.map fV' ≫ W.hom.unop).op =
--     x (u.map fV' ≫ W.hom.unop ≫ f) (by simpa using hV'),
--   { convert H (show S ((u.map fV' ≫ W.hom.unop) ≫ f), by simpa using hV') using 2,
--     simp },
--   simp only [quiver.hom.unop_op, equiv.symm_symm, structured_arrow.map_obj_hom, unop_comp,
--     equiv.coe_fn_mk, functor.comp_map, coyoneda_obj_map, category.assoc, ← this, op_comp,
--     Ran_obj_map, nat_trans.id_app],
--   erw category.id_comp,
--   erw limit.pre_π,
--   congr,
--   convert limit.w (Ran.diagram u.op ℱ.val (op V)) (structured_arrow.hom_mk' W fV'.op),
--   rw structured_arrow.map_mk,
--   erw category.comp_id,
--   simp
-- end

-- /-- Verify that the `glued_section` is an amalgamation of `x`. -/
-- lemma glued_section_is_amalgamation : x.is_amalgamation (glued_section hu ℱ hS hx) :=
-- begin
--   intros V fV hV,
--   ext W,
--   simp only [functor.comp_map, limit.lift_pre, coyoneda_obj_map, Ran_obj_map, glued_section],
--   erw limit.lift_π,
--   symmetry,
--   convert helper hu ℱ hS hx _ (x fV hV) _ _ using 1,
--   intros V' fV' hV',
--   convert hx (fV') (𝟙 _) hV hV' (by simp),
--   simp
-- end

-- /-- Verify that the amalgamation is indeed unique. -/
-- lemma glued_section_is_unique (y) (hy: x.is_amalgamation y) : y = glued_section hu ℱ hS hx :=
-- begin
--   unfold glued_section limit.lift,
--   ext W,
--   erw limit.lift_π,
--   convert helper hu ℱ hS hx (𝟙 _) y W _,
--   { simp },
--   { intros V' fV' hV',
--     convert hy fV' (by simpa using hV'),
--     erw category.comp_id }
-- end

-- end Ran_is_sheaf_of_cover_lifting

/--
If `u` is cover_lifting, then `Ran u.op` pushes sheaves to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00XK,
but without the condition that `C` or `D` has pullbacks.
-/
theorem Ran_is_sheaf_of_cover_lifting {u : C ⥤ D} (hu : cover_preserving J K u) (ℱ : Sheaf K A) :
  presheaf.is_sheaf J (((whiskering_left _ _ _).obj u.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  split, swap,
  {
    change family_of_elements (u.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) ⇑S at x,
    -- simp,
    -- apply presieve.is_sheaf_for.amalgamate,
    apply (ℱ.2 X _ (hu.cover_preserve hS)).amalgamate (x.functor_pushforward u).sieve_extend,
    apply family_of_elements.compatible.sieve_extend,

  },
  split,
  { apply Ran_is_sheaf_of_cover_lifting.glued_section_is_amalgamation },
  { apply Ran_is_sheaf_of_cover_lifting.glued_section_is_unique }
end

end category_theory
