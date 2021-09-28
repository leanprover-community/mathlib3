/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.limits.kan_extension

/-!
# Cocontinuous functors between sites.

We define cocontinuous functors between sites as functors that pulls covering sieves back to
covering sieves. This seems stronger that the definition found in stacks project,
but they are actually equivalent via `category_theory.grothendieck_topology.superset_covering`
(The precise statement not formalized, but follows from it quite trivially).

This concept is also called the "covering lifting property" as defined in [MM92] Chapter VII,
Section 10, and should not be confused with the general definition of cocontinuous functors
between categories as functors preserving small colimits.

## Main Results
- `category_theory.sites.cocontinuous.Ran_is_sheaf`: If `F : C ⥤ D` is cocontinuous, then
`Ran F.op` as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

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
A functor `F : (C, J) ⥤ (D, K)` between sites is called cocontinuous if for all covering sieves
`R` in `D`, `R.pullback F` is a covering sieve in `C`.
-/
structure cocontinuous (J : grothendieck_topology C) (K : grothendieck_topology D) (F : C ⥤ D) :=
(cover_lift : ∀ {U : C} {S : sieve (F.obj U)} (hS : S ∈ K (F.obj U)), S.functor_pullback F ∈ J U)

namespace cocontinuous

/-- A trivial example to make the inhabited linter happy. -/
instance id_cocontinuous : inhabited (cocontinuous J J (𝟭 _)) :=
⟨⟨λ _ S h, by { convert h, simp }⟩⟩


variables {F : C ⥤ D} (HF : cocontinuous J K F)
namespace Ran_is_sheaf
/-
We will now prove that `Ran F.op` maps sheaves to sheaves if `F` is cocontinuous. This can be found
in https://stacks.math.columbia.edu/tag/00XK. However, the proof given here uses the
amalgamation definition of sheaves, and thus does not require that `C` or `D` has catigorical
pullbacks.

Suppose there is a compatible family `x` of elements on `U`, we ought to glue them together
to form a unique section on `S`. We will achieve this by restricting `x` onto objects of the form
`F(Y)` with `Y : C`, and glueing them via the sheaf property of `ℱ` on `C`.
The uniqueness also follows from the uniqueness provided by the sheaf property.
-/
variable (ℱ : Sheaf J A)
variables {X : A} {U : D} {S : sieve U} (hS : S ∈ K U)
variables {x : S.arrows.family_of_elements ((Ran F.op).obj ℱ.val ⋙ coyoneda.obj (op X))}
variable (hx : x.compatible)

include HF hS hx

/-- Given a `F(Y) ⟶ U`, we can find a unique section in `ℱ(Y)` that agrees with `x` on `Y`. -/
lemma get_section (Y : structured_arrow (op U) F.op) :
 ∃! (t : (ℱ.val ⋙ coyoneda.obj (op X)).obj (op (unop Y.right))),
  presieve.family_of_elements.is_amalgamation
    (((x.pullback Y.3.unop).functor_pullback F).comp_presheaf_map
      (show _ ⟶ _, from whisker_right ((Ran.adjunction A F.op).counit.app ℱ.val)
        (coyoneda.obj (op X)))) t :=
begin
  let hom_sh := whisker_right ((Ran.adjunction A F.op).counit.app ℱ.val) (coyoneda.obj (op X)),
  have S' := (K.pullback_stable Y.hom.unop hS),
  have hs' := ((hx.pullback Y.3.unop).functor_pullback F).comp_presheaf_map hom_sh,
  exact ℱ.2 X _ (HF.cover_lift S') _ hs',
end

/-- The limit cone in order to glue the sections obtained via `get_section`. -/
def glued_limit_cone : limits.cone ((structured_arrow.proj (op U) (F.op)) ⋙ ℱ.val) :=
{ X := X, π :=
  { app := λ Y, classical.some (get_section HF ℱ hS hx Y),
    naturality' := λ Y Z f, by
    { simp only [functor.comp_map, structured_arrow.proj_map, functor.const.obj_map],
      erw category.id_comp,
      obtain ⟨Pt₁, _⟩ := classical.some_spec (get_section HF ℱ hS hx Y),
      generalize ht₁ : classical.some (get_section HF ℱ hS hx Y) = t₁,
      rw ht₁ at Pt₁,
      apply unique_of_exists_unique
          (get_section HF ℱ hS hx Z) (classical.some_spec (get_section HF ℱ hS hx Z)).1,
      intros W fw hw,
      dsimp only [comp_presheaf_map,
          family_of_elements.functor_pullback, family_of_elements.pullback],
      have eq := congr_arg quiver.hom.unop f.w,
      erw category.id_comp at eq,
      convert Pt₁ (fw ≫ f.right.unop) (by {
        change S (F.map _ ≫ Y.hom.unop),
        rw eq at hw,
        simpa using hw,
      }) using 3,
      { tidy },
      { simp[eq] } } } }

/--
A helper lemma for the following two lemmas. Basically stating that
if `y` is the amalgamation of `x`, then restricting `y` onto `F(W) ⟶ X` coincides with
`cocontinuous.Ran_is_sheaf.
-/
lemma helper {V} (f : V ⟶ U) (y : ((Ran F.op).obj ℱ.val ⋙ coyoneda.obj (op X)).obj (op V)) (W)
  (H : ∀ {V'} {fV : F.obj V' ⟶ V} (hV),
    ((Ran F.op).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV.op y = x (fV ≫ f) hV) :
  y ≫ limit.π (Ran.diagram F.op ℱ.val (op V)) W =
    (glued_limit_cone HF ℱ hS hx).π.app ((structured_arrow.map f.op).obj W) :=
begin
  apply unique_of_exists_unique
    (get_section HF ℱ hS hx ((structured_arrow.map f.op).obj W)) _
    (classical.some_spec (get_section HF ℱ hS hx ((structured_arrow.map f.op).obj W))).1,
  intros V' fV' hV',
  dsimp only [comp_presheaf_map, Ran.adjunction, Ran.equiv,
    family_of_elements.functor_pullback, family_of_elements.pullback],
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
  convert limit.w (Ran.diagram F.op ℱ.val (op V)) (structured_arrow.hom_mk' W fV'.op),
  rw structured_arrow.map_mk,
  erw category.comp_id,
  simp
end

/-- The obtained section is indeed the amalgamation. -/
lemma glued_section_is_amalgamation : x.is_amalgamation
    (limit.lift (structured_arrow.proj (op U) F.op ⋙ ℱ.val) (glued_limit_cone HF ℱ hS hx)) :=
begin
  intros V fV hV,
  ext W,
  simp only [functor.comp_map, limit.lift_pre, coyoneda_obj_map, Ran_obj_map],
  erw limit.lift_π,
  symmetry,
  apply helper HF ℱ hS hx _ (x fV hV),
  intros V' fV' hV',
  convert hx (fV') (𝟙 _) hV hV' (by simp),
  simp
end

/-- The amalgamation is indeed unique. -/
lemma glued_section_is_unique (y) (hy: x.is_amalgamation y) :
  y = limit.lift (structured_arrow.proj (op U) F.op ⋙ ℱ.val) (glued_limit_cone HF ℱ hS hx) :=
begin
  unfold limit.lift,
  ext W,
  erw limit.lift_π,
  convert helper HF ℱ hS hx (𝟙 _) y W _,
  { cases W, simp },
  { intros V' fV' hV',
    convert hy fV' (by simpa using hV'),
    erw category.comp_id }
end

end Ran_is_sheaf

/--
If `F` is cocontinuous, then `Ran F.op` pushes sheaves to sheaves.
Basically https://stacks.math.columbia.edu/tag/00XK but without the condition that C or D
has pullbacks
-/
lemma Ran_is_sheaf (HF : cocontinuous J K F) (ℱ : Sheaf J A) :
  presheaf.is_sheaf K ((Ran F.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  split, swap,
  { exact limits.limit.lift _ (Ran_is_sheaf.glued_limit_cone HF ℱ hS hx) },
  split,
  { apply Ran_is_sheaf.glued_section_is_amalgamation },
  { apply Ran_is_sheaf.glued_section_is_unique }
end

end cocontinuous
end sites
end category_theory
