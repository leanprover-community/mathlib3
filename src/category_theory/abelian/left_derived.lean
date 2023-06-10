/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Adam Topaz
-/

import category_theory.abelian.homology
import category_theory.functor.left_derived
import category_theory.abelian.projective
import category_theory.limits.constructions.epi_mono

/-!
# Zeroth left derived functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
preadditive.exact_of_iso_of_exact' (F.map (P.complex.d 1 0)) (F.map (P.π.f 0)) _ _
    (homological_complex.X_prev_iso ((F.map_homological_complex _).obj P.complex) rfl).symm
    (iso.refl _) (iso.refl _) (by simp) (by simp)
    (preserves_exact_of_preserves_finite_colimits_of_epi _ (P.exact₀))

/-- Given `P : ProjectiveResolution X`, a morphism `(F.left_derived 0).obj X ⟶ F.obj X`. -/
@[nolint unused_arguments]
def left_derived_zero_to_self_app [enough_projectives C] {X : C}
  (P : ProjectiveResolution X) : (F.left_derived 0).obj X ⟶ F.obj X :=
(left_derived_obj_iso F 0 P).hom ≫ homology.desc' _ _ _ (kernel.ι _ ≫ (F.map (P.π.f 0)))
begin
  rw [kernel.lift_ι_assoc, homological_complex.d_to_eq _ (by simp : (complex_shape.down ℕ).rel 1 0),
    map_homological_complex_obj_d, category.assoc, ← functor.map_comp],
  simp
end

/-- Given `P : ProjectiveResolution X`, a morphism `F.obj X ⟶ (F.left_derived 0).obj X` given
`preserves_finite_colimits F`. -/
def left_derived_zero_to_self_app_inv [enough_projectives C] [preserves_finite_colimits F] {X : C}
  (P : ProjectiveResolution X) : F.obj X ⟶ (F.left_derived 0).obj X :=
begin
  refine ((as_iso (cokernel.desc _ _ (exact_of_map_projective_resolution F P).w)).inv) ≫ _ ≫
    (homology_iso_cokernel_lift _ _ _).inv ≫ (left_derived_obj_iso F 0 P).inv,
  exact cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) (by { ext, simp }),
end

lemma left_derived_zero_to_self_app_comp_inv [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : left_derived_zero_to_self_app F P ≫
  left_derived_zero_to_self_app_inv F P = 𝟙 _ :=
begin
  dsimp [left_derived_zero_to_self_app, left_derived_zero_to_self_app_inv],
  rw [← category.assoc, ← category.assoc, ← category.assoc, iso.comp_inv_eq, category.id_comp,
    category.assoc, category.assoc, category.assoc],
  convert category.comp_id _,
  rw [← category.assoc, ← category.assoc, iso.comp_inv_eq, category.id_comp],
  ext,
  rw [← category.assoc, ← category.assoc, homology.π'_desc', category.assoc, category.assoc,
    ← category.assoc (F.map _), abelian.cokernel.desc.inv, cokernel.π_desc, homology.π',
    category.assoc, iso.inv_hom_id, category.comp_id, ← category.assoc],
  convert category.id_comp _ using 2,
  ext,
  rw [category.id_comp, category.assoc, equalizer_as_kernel, kernel.lift_ι, category.comp_id],
end

lemma left_derived_zero_to_self_app_inv_comp [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : left_derived_zero_to_self_app_inv F P ≫
  left_derived_zero_to_self_app F P = 𝟙 _ :=
begin
  dsimp [left_derived_zero_to_self_app, left_derived_zero_to_self_app_inv],
  rw [category.assoc, category.assoc, category.assoc,
    ← category.assoc (F.left_derived_obj_iso 0 P).inv, iso.inv_hom_id, category.id_comp,
    is_iso.inv_comp_eq, category.comp_id],
  ext,
  simp only [cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, homology.desc'],
  rw [← category.assoc, ← category.assoc (homology_iso_cokernel_lift _ _ _).inv, iso.inv_hom_id,
    category.id_comp],
  simp only [category.assoc, cokernel.π_desc, kernel.lift_ι_assoc, category.id_comp],
end

/-- Given `P : ProjectiveResolution X`, the isomorphism `(F.left_derived 0).obj X ≅ F.obj X` if
`preserves_finite_colimits F`. -/
def left_derived_zero_to_self_app_iso [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : (F.left_derived 0).obj X ≅ F.obj X :=
{ hom := left_derived_zero_to_self_app _ P,
  inv := left_derived_zero_to_self_app_inv _ P,
  hom_inv_id' := left_derived_zero_to_self_app_comp_inv _ P,
  inv_hom_id' := left_derived_zero_to_self_app_inv_comp _ P }

/-- Given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `left_derived_zero_to_self_obj_hom. -/
lemma left_derived_zero_to_self_natural [enough_projectives C] {X : C} {Y : C} (f : X ⟶ Y)
  (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
  (F.left_derived 0).map f ≫ left_derived_zero_to_self_app F Q =
  left_derived_zero_to_self_app F P ≫ F.map f :=
begin
  dsimp only [left_derived_zero_to_self_app],
  rw [functor.left_derived_map_eq F 0 f (ProjectiveResolution.lift f P Q) (by simp),
    category.assoc, category.assoc, ← category.assoc _ (F.left_derived_obj_iso 0 Q).hom,
    iso.inv_hom_id, category.id_comp, category.assoc, whisker_eq],
  dsimp only [homology_functor_map],
  ext,
  simp only [homological_complex.hom.sq_to_right, map_homological_complex_map_f,
    homology.π'_map_assoc, homology.π'_desc', kernel.lift_ι_assoc, category.assoc,
    homology.π'_desc'_assoc, ← map_comp, show (ProjectiveResolution.lift f P Q).f 0 ≫ _ = _ ≫ f,
    from homological_complex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0],
end

/-- Given `preserves_finite_colimits F`, the natural isomorphism `(F.left_derived 0) ≅ F`. -/
def left_derived_zero_iso_self [enough_projectives C] [preserves_finite_colimits F] :
  (F.left_derived 0) ≅ F :=
nat_iso.of_components (λ X, left_derived_zero_to_self_app_iso _ (ProjectiveResolution.of X))
  (λ X Y f, left_derived_zero_to_self_natural _ _ _ _)

end category_theory.abelian.functor
