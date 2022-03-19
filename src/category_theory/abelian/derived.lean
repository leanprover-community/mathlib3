/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Adam Topaz
-/

import category_theory.abelian.homology
import category_theory.functor.derived
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
begin
  have : (complex_shape.down ℕ).rel 1 0 := rfl,
  let f := (homological_complex.X_prev_iso ((F.map_homological_complex _).obj P.complex) this),
  exact preadditive.exact_of_iso_of_exact' (F.map (P.complex.d 1 0)) (F.map (P.π.f 0)) _ _
    f.symm (iso.refl _) (iso.refl _) (by simp) (by simp)
    (preserves_exact_of_preserves_finite_colimits_of_epi _ (P.exact₀)),
end

/-- Given `P : ProjectiveResolution X`, a morphism `(F.left_derived 0).obj X ⟶ F.obj X`. -/
@[nolint unused_arguments]
def left_derived_zero_to_self_app [enough_projectives C] {X : C}
  (P : ProjectiveResolution X) : (F.left_derived 0).obj X ⟶ F.obj X :=
(left_derived_obj_iso F 0 P).hom ≫ homology.desc' _ _ _ (kernel.ι _ ≫ (F.map (P.π.f 0)))
begin
  { have : (complex_shape.down ℕ).rel 1 0 := rfl,
    rw [kernel.lift_ι_assoc, homological_complex.d_to_eq _ this, map_homological_complex_obj_d,
      category.assoc, ← functor.map_comp],
    simp },
end
≫ F.map (𝟙 _)

/-- Given `P : ProjectiveResolution X`, a morphism `F.obj X ⟶ (F.left_derived 0).obj X` given
`preserves_finite_colimits F`. -/
@[nolint unused_arguments]
def left_derived_zero_to_self_app_inv [enough_projectives C] [preserves_finite_colimits F] {X : C}
  (P : ProjectiveResolution X) : F.obj X ⟶ (F.left_derived 0).obj X :=
begin
  haveI ex := (exact_of_map_projective_resolution F P),
  refine ((as_iso (cokernel.desc _ _ ex.w)).inv) ≫ _ ≫ (homology_iso_cokernel_lift _ _ _).inv ≫
    (left_derived_obj_iso F 0 P).inv,
  exact cokernel.map _ _ (𝟙 _) (kernel.lift _ (𝟙 _) (by simp)) (by { ext, simp }),
end

lemma left_derived_zero_to_self_app_comp_inv [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : left_derived_zero_to_self_app F P ≫
  left_derived_zero_to_self_app_inv F P = 𝟙 _ :=
begin
  dsimp [left_derived_zero_to_self_app, left_derived_zero_to_self_app_inv],
  rw [map_id, category.comp_id, category.assoc],
  refine (iso.eq_inv_comp _).1 _,
  rw [← category.assoc, ← category.assoc, ← category.assoc],
  refine (iso.comp_inv_eq _).2 _,
  rw [category.comp_id, iso.inv_hom_id, iso.comp_inv_eq, category.id_comp],
  ext,
  simp [category.assoc, homology.π'_desc'_assoc,
    cokernel.π_desc, homology.π', iso.inv_hom_id, category.comp_id],
  nth_rewrite 1 [← category.comp_id (cokernel.π _)],
  refine congr_arg (category_struct.comp _) _,
  dsimp [homology.desc'],
  rw [← category.assoc, ← category.assoc, ← category.assoc, iso.inv_hom_id, category.id_comp],
  ext,
  simp [coequalizer_as_cokernel, category.assoc, cokernel.π_desc_assoc,
    cokernel.π_desc, category.comp_id],
  rw [← category.assoc],
  nth_rewrite 1 [← category.id_comp (cokernel.π _)],
  refine congr_fun (congr_arg category_struct.comp _) _,
  ext,
  simp only [category.assoc, kernel.lift_ι, category.comp_id, category.id_comp],
end

lemma left_derived_zero_to_self_app_inv_comp [enough_projectives C] [preserves_finite_colimits F]
  {X : C} (P : ProjectiveResolution X) : left_derived_zero_to_self_app_inv F P ≫
  left_derived_zero_to_self_app F P = 𝟙 _ :=
begin
  dsimp [left_derived_zero_to_self_app, left_derived_zero_to_self_app_inv],
  rw [map_id, category.comp_id, category.assoc, category.assoc, category.assoc,
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
  let f₁ := ProjectiveResolution.lift f P Q,
  rw [functor.left_derived_map_eq F 0 f f₁ (by simp),
    category.assoc, category.assoc, ← category.assoc _ (F.left_derived_obj_iso 0 Q).hom,
    iso.inv_hom_id, category.id_comp, category.assoc, category.assoc],
  congr' 1,
  rw [map_id, map_id, category.id_comp, category.comp_id],
  dsimp only [homology_functor_map],
  ext,
  simp only [homological_complex.hom.sq_to_right, map_homological_complex_map_f,
    homology.π'_map_assoc, homology.π'_desc', kernel.lift_ι_assoc, category.assoc,
    homology.π'_desc'_assoc],
  rw [← functor.map_comp, ← functor.map_comp],
  congr' 2,
  exact homological_complex.congr_hom (ProjectiveResolution.lift_commutes f P Q) 0
end

/-- Given `preserves_finite_colimits F`, the natural isomorphism `(F.left_derived 0) ≅ F`. -/
def left_derived_zero_iso_self [enough_projectives C] [preserves_finite_colimits F] :
  (F.left_derived 0) ≅ F :=
nat_iso.of_components (λ X, left_derived_zero_to_self_app_iso _ (ProjectiveResolution.of X))
  (λ X Y f, left_derived_zero_to_self_natural _ _ _ _)

end category_theory.abelian.functor
