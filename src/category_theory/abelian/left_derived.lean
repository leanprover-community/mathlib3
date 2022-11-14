/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Adam Topaz
-/

import category_theory.functor.left_derived
import category_theory.abelian.projective
import category_theory.limits.constructions.epi_mono

/-!
# Zeroth left derived functors

If `F : C ⥤ D` is an additive right exact functor between abelian categories, where `C` has enough
projectives, we provide the natural isomorphism `F.left_derived 0 ≅ F`.

## Main definitions

* `category_theory.abelian.functor.left_derived_zero_iso_self`: the natural isomorphism
  `(F.left_derived 0) ≅ F`.

## Main results
* `preserves_exact_of_preserves_finite_colimits_of_epi`: if `preserves_finite_colimits F` and
  `epi g`, then `exact (F.map f) (F.map g)` if `exact f g`.

-/

noncomputable theory

universes w v u

open category_theory.limits category_theory category_theory.functor

variables {C : Type u} [category.{w} C] {D : Type u} [category.{w} D]
variables (F : C ⥤ D) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

namespace category_theory.abelian.functor

open category_theory.preadditive

variables [abelian C] [abelian D] [additive F]

/-- If `preserves_finite_colimits F` and `epi g`, then `exact (F.map f) (F.map g)` if
`exact f g`. -/
lemma preserves_exact_of_preserves_finite_colimits_of_epi [preserves_finite_colimits F] [epi g]
  (ex : exact f g) : exact (F.map f) (F.map g) :=
abelian.exact_of_is_cokernel _ _ (by simp [← functor.map_comp, ex.w])
  $ limits.is_colimit_cofork_map_of_is_colimit' _ ex.w (abelian.is_colimit_of_exact_of_epi _ _ ex)

lemma exact_of_map_projective_resolution (P: ProjectiveResolution X) [preserves_finite_colimits F] :
  exact (((F.map_homological_complex (complex_shape.down ℕ)).obj P.complex).d_to 0)
  (F.map (P.π.f 0)) :=
exact_of_iso_of_exact (F.map (P.complex.d 1 0)) (F.map (P.π.f 0)) _ _
    (homological_complex.X_prev_iso ((F.map_homological_complex _).obj P.complex) rfl).symm
    (iso.refl _) (iso.refl _) (by simp) (by simp)
    (preserves_exact_of_preserves_finite_colimits_of_epi _ (P.exact₀))

/-- The isomorphism `(F.left_derived 0).obj X ≅ F.obj X` if
`preserves_finite_colimits F`. -/
def left_derived_zero_iso_self_app [enough_projectives C] [preserves_finite_colimits F]
  (X : C) : (F.left_derived 0).obj X ≅ F.obj X :=
begin
  let P := (has_projective_resolution.out X).some,
  exact (homotopy_category.homology_factors D (complex_shape.down ℕ) 0).app
    ((F.map_homological_complex _).obj P.complex) ≪≫ F.homology_iso (P.complex.sc' 0) ≪≫
    F.map_iso P.homology_data_complex_zero.homology_iso,
end

/-- Given a morphism `f : X ⟶ Y`,
naturality of the square given by `left_derived_zero_to_self_obj_hom. -/
lemma left_derived_zero_iso_self_naturality [enough_projectives C] {X : C} {Y : C} (f : X ⟶ Y)
  [preserves_finite_colimits F] :
  (F.left_derived 0).map f ≫ (left_derived_zero_iso_self_app F Y).hom =
    (left_derived_zero_iso_self_app F X).hom ≫ F.map f :=
sorry
--begin
--  dsimp only [left_derived_zero_to_self_app],
--  rw [functor.left_derived_map_eq F 0 f (ProjectiveResolution.lift f P Q) (by simp),
--    category.assoc, category.assoc, ← category.assoc _ (F.left_derived_obj_iso 0 Q).hom,
--    iso.inv_hom_id, category.id_comp, category.assoc, whisker_eq],
--  dsimp only [homology_functor_map],
--  ext,
--  simp only [homological_complex.hom.sq_to_right, map_homological_complex_map_f,
--    homology.π'_map_assoc, homology.π'_desc', kernel.lift_ι_assoc, category.assoc,
--    homology.π'_desc'_assoc, ← map_comp, show (ProjectiveResolution.lift f P Q).f 0 ≫ _ = _ ≫ f,
--    from homological_complex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0],
--end

/-- Given `preserves_finite_colimits F`, the natural isomorphism `(F.left_derived 0) ≅ F`. -/
def left_derived_zero_iso_self [enough_projectives C] [preserves_finite_colimits F] :
  (F.left_derived 0) ≅ F :=
nat_iso.of_components (left_derived_zero_iso_self_app F)
  (λ X Y f, left_derived_zero_iso_self_naturality F f)

end category_theory.abelian.functor
