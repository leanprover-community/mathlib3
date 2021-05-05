/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.projective_resolution

/-!
# Left-derived functors

We define the left-derived functors `F.left_derived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

The definition is
```
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick a projective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these left-derived functors can be calculated
on objects using any choice of projective resolution,
and on morphisms by any choice of lift to a chain map between chosen projective resolutions.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Implementation

We don't assume the categories involved are abelian
(just preadditive, and have equalizers, cokernels, and image maps),
or that the functors are right exact.
None of these assumptions are needed yet.

It is often convenient, of course, to work with `[abelian C] [enough_projectives C] [abelian D]`
which (assuming the results from `category_theory.abelian.projective`) are enough to
provide all the typeclass hypotheses assumed here.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C] {D : Type*} [category D]

-- Importing `category_theory.abelian.projective` and assuming
-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
variables [preadditive C] [has_zero_object C] [has_equalizers C]
  [has_images C] [has_projective_resolutions C]
variables [preadditive D] [has_zero_object D] [has_equalizers D] [has_cokernels D]
  [has_images D] [has_image_maps D]

/-- The left derived functors of an additive functor. -/
def functor.left_derived (F : C ⥤ D) [F.additive] (n : ℕ) : C ⥤ D :=
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n

-- TODO the left derived functors are additive (and linear when `F` is linear)

/-- We can compute a left derived functor using a chosen projective resolution. -/
def functor.left_derived_obj_iso (F : C ⥤ D) [F.additive] (n : ℕ)
  {X : C} (P : ProjectiveResolution X) :
  (F.left_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P.complex) :=
(homotopy_category.homology_functor D _ n).map_iso
  (homotopy_category.iso_of_homotopy_equiv
    (F.map_homotopy_equiv (ProjectiveResolution.homotopy_equiv _ P)))
  ≪≫ (homotopy_category.homology_factors D _ n).app _

/-- The 0-th derived functor on a projective object `X` is just `X`. -/
def functor.left_derived_obj_projective_zero (F : C ⥤ D) [F.additive]
  (X : C) [projective X] :
  (F.left_derived 0).obj X ≅ F.obj X :=
F.left_derived_obj_iso 0 (ProjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((chain_complex.single_0_map_homological_complex F).app X) ≪≫
  (chain_complex.homology_functor_0_single_0 D).app (F.obj X)

local attribute [instance] has_zero_object.has_zero

/-- The higher derived functors vanish on projective objects. -/
def functor.left_derived_obj_projective_succ (F : C ⥤ D) [F.additive] (n : ℕ)
  (X : C) [projective X] :
  (F.left_derived (n+1)).obj X ≅ 0 :=
F.left_derived_obj_iso (n+1) (ProjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((chain_complex.single_0_map_homological_complex F).app X) ≪≫
  (chain_complex.homology_functor_succ_single_0 D n).app (F.obj X)

/--
We can compute a left derived functor on a morphism using a lift of that morphism
to a chain map between chosen projective resolutions.
-/
lemma functor.left_derived_map_eq (F : C ⥤ D) [F.additive] (n : ℕ) {X Y : C} (f : X ⟶ Y)
  {P : ProjectiveResolution X} {Q : ProjectiveResolution Y} (g : P.complex ⟶ Q.complex)
  (w : g ≫ Q.π = P.π ≫ (chain_complex.single_0 C).map f) :
  (F.left_derived n).map f =
  (F.left_derived_obj_iso n P).hom ≫
    (homology_functor D _ n).map ((F.map_homological_complex _).map g) ≫
    (F.left_derived_obj_iso n Q).inv :=
begin
  dsimp only [functor.left_derived, functor.left_derived_obj_iso],
  dsimp, simp only [category.comp_id, category.id_comp],
  rw homotopy_category.homology_functor_map_factors,
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  apply functor.map_homotopy,
  apply homotopy.trans,
  exact homotopy_category.homotopy_out_map _,
  apply ProjectiveResolution.lift_homotopy f,
  { simp, },
  { simp [w], },
end

/-- The natural transformation between left-derived functors induced by a natural transformation. -/
def nat_trans.left_derived {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ) :
  F.left_derived n ⟶ G.left_derived n :=
whisker_left (projective_resolutions C)
  (whisker_right (nat_trans.map_homotopy_category α _)
    (homotopy_category.homology_functor D _ n))

/--
A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution.
-/
lemma nat_trans.left_derived_eq {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ)
  {X : C} (P : ProjectiveResolution X) :
  (nat_trans.left_derived α n).app X =
    (F.left_derived_obj_iso n P).hom ≫
      (homology_functor D _ n).map ((nat_trans.map_homological_complex α _).app P.complex) ≫
        (G.left_derived_obj_iso n P).inv :=
begin
  symmetry,
  dsimp [nat_trans.left_derived, functor.left_derived_obj_iso],
  simp only [category.comp_id, category.id_comp],
  rw homotopy_category.homology_functor_map_factors,
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  simp only [nat_trans.map_homological_complex_naturality_assoc,
    ←functor.map_comp],
  apply homotopy.comp_left_id,
  rw [←functor.map_id],
  apply functor.map_homotopy,
  apply homotopy_equiv.homotopy_hom_inv_id,
end

-- TODO:
-- lemma nat_trans.left_derived_projective_zero {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
--   (X : C) [projective X] :
--   (nat_trans.left_derived α 0).app X =
--     (F.left_derived_obj_projective_zero X).hom ≫
--       α.app X ≫
--         (G.left_derived_obj_projective_zero X).inv := sorry

-- TODO:
-- lemma nat_trans.left_derived_projective_succ {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
--   (n : ℕ) (X : C) [projective X] :
--   (nat_trans.left_derived α (n+1)).app X = 0 := sorry

-- TODO left-derived functors of the identity functor are the identity
-- (requires we assume `abelian`?)
-- PROJECT left-derived functors of a composition (Grothendieck sequence)

end category_theory
