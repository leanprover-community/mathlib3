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

/-- The isomorphism `(F.left_derived 0).obj X ≅ F.obj X` if `preserves_finite_colimits F`. -/
def left_derived_zero_iso_self_app [enough_projectives C] [preserves_finite_colimits F]
  (X : C) : (F.left_derived 0).obj X ≅ F.obj X :=
((has_projective_resolution.out X).some.homology_data_complex_zero.map F).homology_iso

/-- Given a morphism `f : X ⟶ Y`,
naturality of the square given by `left_derived_zero_to_self_obj_hom. -/
lemma left_derived_zero_iso_self_naturality [enough_projectives C] {X : C} {Y : C} (f : X ⟶ Y)
  [preserves_finite_colimits F] :
  (F.left_derived 0).map f ≫ (left_derived_zero_iso_self_app F Y).hom =
    (left_derived_zero_iso_self_app F X).hom ≫ F.map f :=
begin
  let P := (has_projective_resolution.out X).some,
  let Q := (has_projective_resolution.out Y).some,
  let h := ProjectiveResolution.homology_map_data_zero f P Q
    (ProjectiveResolution.lift f P Q)
    (by rw [← homological_complex.comp_f, ProjectiveResolution.lift_commutes,
      homological_complex.comp_f, chain_complex.single₀_map_f_0]),
  refine eq.trans _ (h.map F).homology_map_comm,
  change (homology_functor D _ 0).map ((F.map_homological_complex _).map _) ≫ _ =
    (homology_functor D _ 0).map ((F.map_homological_complex _).map _) ≫ _,
  simp only [homotopy_category.homology_functor_map_factors],
  congr' 2,
  apply homotopy_category.eq_of_homotopy,
  apply F.map_homotopy,
  apply homotopy_category.homotopy_of_eq,
  apply homotopy_category.quotient_map_out,
end

/-- Given `preserves_finite_colimits F`, the natural isomorphism `(F.left_derived 0) ≅ F`. -/
def left_derived_zero_iso_self [enough_projectives C] [preserves_finite_colimits F] :
  (F.left_derived 0) ≅ F :=
nat_iso.of_components (left_derived_zero_iso_self_app F)
  (λ X Y f, left_derived_zero_iso_self_naturality F f)

end category_theory.abelian.functor
