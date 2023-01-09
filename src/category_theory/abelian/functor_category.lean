/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.abelian.exact
import category_theory.preadditive.functor_category
import category_theory.limits.shapes.functor_category
import category_theory.limits.preserves.shapes.kernels
import algebra.homology.exact

/-!
# If `D` is abelian, then the functor category `C ⥤ D` is also abelian.

-/

noncomputable theory

namespace category_theory
open category_theory.limits

namespace abelian

section
universes z w v u
variables {C : Type (max v u)} [category.{v} C]
variables {D : Type w} [category.{max z v u} D] [abelian D]

namespace functor_category
variables {F G : C ⥤ D} (α : F ⟶ G) (X : C)

/-- The abelian coimage in a functor category can be calculated componentwise. -/
@[simps]
def coimage_obj_iso : (abelian.coimage α).obj X ≅ abelian.coimage (α.app X) :=
preserves_cokernel.iso ((evaluation C D).obj X) _ ≪≫
  cokernel.map_iso _ _ (preserves_kernel.iso ((evaluation C D).obj X) _) (iso.refl _)
  begin
    dsimp,
    simp only [category.comp_id],
    exact (kernel_comparison_comp_ι _ ((evaluation C D).obj X)).symm,
  end

/-- The abelian image in a functor category can be calculated componentwise. -/
@[simps]
def image_obj_iso : (abelian.image α).obj X ≅ abelian.image (α.app X) :=
preserves_kernel.iso ((evaluation C D).obj X) _ ≪≫
  kernel.map_iso _ _ (iso.refl _) (preserves_cokernel.iso ((evaluation C D).obj X) _)
  begin
    apply (cancel_mono (preserves_cokernel.iso ((evaluation C D).obj X) α).inv).1,
    simp only [category.assoc, iso.hom_inv_id],
    dsimp,
    simp only [category.id_comp, category.comp_id],
    exact (π_comp_cokernel_comparison _ ((evaluation C D).obj X)).symm,
  end

lemma coimage_image_comparison_app :
  coimage_image_comparison (α.app X) =
    (coimage_obj_iso α X).inv ≫ (coimage_image_comparison α).app X ≫ (image_obj_iso α X).hom :=
begin
  ext,
  dsimp,
  simp only [category.comp_id, category.id_comp, category.assoc,
    coimage_image_factorisation, limits.cokernel.π_desc_assoc, limits.kernel.lift_ι],
  simp only [←evaluation_obj_map C D X],
  erw kernel_comparison_comp_ι _ ((evaluation C D).obj X),
  erw π_comp_cokernel_comparison_assoc _ ((evaluation C D).obj X),
  simp only [←functor.map_comp],
  simp only [coimage_image_factorisation, evaluation_obj_map],
end

lemma coimage_image_comparison_app' :
  (coimage_image_comparison α).app X =
    (coimage_obj_iso α X).hom ≫ coimage_image_comparison (α.app X) ≫ (image_obj_iso α X).inv :=
by simp only [coimage_image_comparison_app, iso.hom_inv_id_assoc, iso.hom_inv_id, category.assoc,
  category.comp_id]

instance functor_category_is_iso_coimage_image_comparison :
  is_iso (abelian.coimage_image_comparison α) :=
begin
  haveI : ∀ X : C, is_iso ((abelian.coimage_image_comparison α).app X),
  { intros, rw coimage_image_comparison_app', apply_instance, },
  apply nat_iso.is_iso_of_is_iso_app,
end

end functor_category

def nat_trans.kernel_obj_iso {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (kernel η).obj X ≅ kernel (η.app X) :=
sorry --((limit.is_limit _).cone_point_unique_up_to_iso η.is_limit_kernel_fork).app X

@[simp, reassoc]
lemma nat_trans.kernel_obj_iso_inv_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (nat_trans.kernel_obj_iso η X).inv ≫ (kernel.ι η).app X = kernel.ι _ :=
sorry --by simp [iso.inv_comp_eq]

@[simp, reassoc]
lemma nat_trans.kernel_obj_iso_hom_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (nat_trans.kernel_obj_iso η X).hom ≫ kernel.ι (η.app X) = (kernel.ι η).app X :=
sorry /-begin
  have h := ((limit.is_limit _).unique_up_to_iso η.is_limit_kernel_fork).hom.w
    walking_parallel_pair.zero,
  apply_fun (λ e, e.app X) at h,
  exact h
end-/

def nat_trans.cokernel_obj_iso {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (cokernel η).obj X ≅ cokernel (η.app X) :=
sorry --((colimit.is_colimit _).cocone_point_unique_up_to_iso η.is_colimit_cokernel_cofork).app X

@[simp, reassoc]
lemma nat_trans.cokernel_obj_iso_π_hom {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  (cokernel.π η).app X ≫ (nat_trans.cokernel_obj_iso η X).hom = cokernel.π _ :=
sorry /-begin
  have h := ((colimit.is_colimit _).unique_up_to_iso η.is_colimit_cokernel_cofork).hom.w
    walking_parallel_pair.one,
  apply_fun (λ e, e.app X) at h,
  exact h,
end-/

@[simp, reassoc]
lemma nat_trans.cokernel_obj_iso_π_inv {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
  cokernel.π (η.app X) ≫ (nat_trans.cokernel_obj_iso η X).inv = (cokernel.π η).app X :=
sorry --by simp [iso.comp_inv_eq]

noncomputable instance functor_category_abelian : abelian (C ⥤ D) :=
abelian.of_coimage_image_comparison_is_iso

theorem nat_trans.exact_iff_forall {F G H : C ⥤ D} (η : F ⟶ G) (γ : G ⟶ H) :
  exact η γ ↔ (∀ j, exact (η.app j) (γ.app j)) :=
begin
  simp_rw abelian.exact_iff,
  split,
  { rintros ⟨h1,h2⟩ j,
    split,
    { apply_fun (λ e, e.app j) at h1, simpa using h1 },
    { apply_fun (λ e, e.app j) at h2,
      simp only [nat_trans.comp_app, nat_trans.app_zero] at h2,
      let eK : (kernel γ).obj j ≅ kernel (γ.app j) := nat_trans.kernel_obj_iso γ j,
      let eQ : (cokernel η).obj j ≅ cokernel (η.app j) := nat_trans.cokernel_obj_iso η j,
      have : kernel.ι (γ.app j) = eK.inv ≫ (kernel.ι γ).app j, by simp, rw this, clear this,
      have : cokernel.π (η.app j) = (cokernel.π η).app j ≫ eQ.hom, by simp, rw this, clear this,
      simp only [category.assoc, reassoc_of h2, zero_comp, comp_zero] } },
  { intros h,
    split,
    { ext j,
      exact (h j).1 },
    { ext j,
      dsimp,
      let eK : (kernel γ).obj j ≅ kernel (γ.app j) := nat_trans.kernel_obj_iso γ j,
      let eQ : (cokernel η).obj j ≅ cokernel (η.app j) := nat_trans.cokernel_obj_iso η j,
      have : (kernel.ι γ).app j = eK.hom ≫ kernel.ι _, by simp, rw this, clear this,
      have : (cokernel.π η).app j = cokernel.π _ ≫ eQ.inv, by simp, rw this, clear this,
      simp only [category.assoc, reassoc_of (h j).2, comp_zero, zero_comp] } },
end

end

section

universes u
variables {C : Type u} [small_category C]
variables {D : Type (u+1)} [large_category D] [abelian D]

/-- A variant with specialized universes for a common case. -/
noncomputable instance functor_category_abelian' : abelian (C ⥤ D) :=
abelian.functor_category_abelian.{u u+1 u u}

end

end abelian

end category_theory
