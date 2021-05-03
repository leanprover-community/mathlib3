/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.projective_resolution

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C] {D : Type*} [category D]

-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
variables [preadditive C] [has_zero_object C] [has_equalizers C] [has_cokernels C]
  [has_images C] [has_image_maps C] [has_projective_resolutions C]
variables [preadditive D] [has_zero_object D] [has_equalizers D] [has_cokernels D]
  [has_images D] [has_image_maps D]

/-- The left derived functors of an additive functor. -/
def functor.left_derived (n : ℕ) (F : C ⥤ D) [F.additive] : C ⥤ D :=
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n

/-- We can compute a left derived functor using a chosen projective resolution. -/
def functor.left_derived_obj_iso (n : ℕ) (F : C ⥤ D) [F.additive]
  (X : C) (P : ProjectiveResolution X) :
  (F.left_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P.complex) :=
(homotopy_category.homology_functor D _ n).map_iso
  (homotopy_category.iso_of_homotopy_equiv
    (F.map_homotopy_equiv (ProjectiveResolution.homotopy_equiv _ P)))
  ≪≫ (homotopy_category.homology_factors D _ n).app _

/--
We can compute a left derived functor on a morphism using a lift of that morphism
to a chain map between chosen projective resolutions.
-/
lemma functor.left_derived_map_eq (n : ℕ) (F : C ⥤ D) [F.additive] {X Y : C} (f : X ⟶ Y)
  (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) (g : P.complex ⟶ Q.complex)
  (w : g ≫ Q.π = P.π ≫ (homological_complex.single C _ 0).map f) :
  (F.left_derived n).map f =
  (F.left_derived_obj_iso n X P).hom ≫
    (homology_functor D _ n).map ((F.map_homological_complex _).map g) ≫
    (F.left_derived_obj_iso n Y Q).inv :=
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
def nat_trans.left_derived (n : ℕ) {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) :
  F.left_derived n ⟶ G.left_derived n :=
whisker_left (projective_resolutions C)
  (whisker_right (nat_trans.map_homotopy_category α _)
    (homotopy_category.homology_functor D _ n))

/--
A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution.
-/
lemma nat_trans.left_derived_eq (n : ℕ) {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
  (X : C) (P : ProjectiveResolution X) :
  (nat_trans.left_derived n α).app X =
    (F.left_derived_obj_iso n X P).hom ≫
      (homology_functor D _ n).map ((nat_trans.map_homological_complex α _).app P.complex) ≫
        (G.left_derived_obj_iso n X P).inv :=
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


-- TODO calculate on projective objects
-- TODO left-derived functors of the identity functor
-- PROJECT left-derived functors of a composition (Grothendieck sequence)

end category_theory
