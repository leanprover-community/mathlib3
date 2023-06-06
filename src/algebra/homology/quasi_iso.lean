/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import algebra.homology.homotopy
import category_theory.abelian.homology

/-!
# Quasi-isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Define the derived category as the localization at quasi-isomorphisms?
-/

open category_theory
open category_theory.limits

universes v u

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V] [has_zero_object V]
variables [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]
variables {c : complex_shape ι} {C D E : homological_complex V c}

/--
A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class quasi_iso (f : C ⟶ D) : Prop :=
(is_iso : ∀ i, is_iso ((homology_functor V c i).map f))

attribute [instance] quasi_iso.is_iso

@[priority 100]
instance quasi_iso_of_iso (f : C ⟶ D) [is_iso f] : quasi_iso f :=
{ is_iso := λ i, begin
    change is_iso (((homology_functor V c i).map_iso (as_iso f)).hom),
    apply_instance,
  end }

instance quasi_iso_comp (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso g] : quasi_iso (f ≫ g) :=
{ is_iso := λ i, begin
    rw functor.map_comp,
    apply_instance,
  end }

lemma quasi_iso_of_comp_left (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso (f ≫ g)] :
  quasi_iso g :=
{ is_iso := λ i, is_iso.of_is_iso_fac_left ((homology_functor V c i).map_comp f g).symm }

lemma quasi_iso_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [quasi_iso g] [quasi_iso (f ≫ g)] :
  quasi_iso f :=
{ is_iso := λ i, is_iso.of_is_iso_fac_right ((homology_functor V c i).map_comp f g).symm }

namespace homotopy_equiv

section
variables {W : Type*} [category W] [preadditive W] [has_cokernels W] [has_images W]
  [has_equalizers W] [has_zero_object W] [has_image_maps W]

/-- An homotopy equivalence is a quasi-isomorphism. -/
lemma to_quasi_iso {C D : homological_complex W c} (e : homotopy_equiv C D) :
  quasi_iso e.hom :=
⟨λ i, begin
  refine ⟨⟨(homology_functor W c i).map e.inv, _⟩⟩,
  simp only [← functor.map_comp, ← (homology_functor W c i).map_id],
  split; apply homology_map_eq_of_homotopy,
  exacts [e.homotopy_hom_inv_id, e.homotopy_inv_hom_id],
end⟩

lemma to_quasi_iso_inv {C D : homological_complex W c} (e : homotopy_equiv C D) (i : ι) :
  (@as_iso _ _ _ _ _ (e.to_quasi_iso.1 i)).inv = (homology_functor W c i).map e.inv :=
begin
  symmetry,
  simp only [←iso.hom_comp_eq_id, as_iso_hom, ←functor.map_comp, ←(homology_functor W c i).map_id,
    homology_map_eq_of_homotopy e.homotopy_hom_inv_id _],
end

end
end homotopy_equiv
namespace homological_complex.hom
section to_single₀
variables {W : Type*} [category W] [abelian W]

section
variables {X : chain_complex W ℕ} {Y : W} (f : X ⟶ ((chain_complex.single₀ _).obj Y))
  [hf : quasi_iso f]

/-- If a chain map `f : X ⟶ Y[0]` is a quasi-isomorphism, then the cokernel of the differential
`d : X₁ → X₀` is isomorphic to `Y.` -/
noncomputable def to_single₀_cokernel_at_zero_iso : cokernel (X.d 1 0) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (hf.1 0)).trans
  ((chain_complex.homology_functor_0_single₀ W).app Y)))

lemma to_single₀_cokernel_at_zero_iso_hom_eq [hf : quasi_iso f] :
  f.to_single₀_cokernel_at_zero_iso.hom = cokernel.desc (X.d 1 0) (f.f 0)
    (by rw ←f.2 1 0 rfl; exact comp_zero) :=
begin
  ext,
  dunfold to_single₀_cokernel_at_zero_iso chain_complex.homology_zero_iso homology_of_zero_right
    homology.map_iso chain_complex.homology_functor_0_single₀ cokernel.map,
  dsimp,
  simp only [cokernel.π_desc, category.assoc, homology.map_desc, cokernel.π_desc_assoc],
  simp [homology.desc, iso.refl_inv (X.X 0)],
end

lemma to_single₀_epi_at_zero [hf : quasi_iso f] :
  epi (f.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  rw [←cokernel.π_desc (X.d 1 0) (f.f 0) (by rw ←f.2 1 0 rfl; exact comp_zero),
    ←to_single₀_cokernel_at_zero_iso_hom_eq] at Hgh,
  rw (@cancel_epi _ _ _ _ _ _ (epi_comp _ _) _ _).1 Hgh,
end

lemma to_single₀_exact_d_f_at_zero [hf : quasi_iso f] :
  exact (X.d 1 0) (f.f 0) :=
begin
  rw preadditive.exact_iff_homology_zero,
  have h : X.d 1 0 ≫ f.f 0 = 0,
  { simp only [← f.2 1 0 rfl, chain_complex.single₀_obj_X_d, comp_zero], },
  refine ⟨h, nonempty.intro (homology_iso_kernel_desc _ _ _ ≪≫ _)⟩,
  { suffices : is_iso (cokernel.desc _ _ h),
    { haveI := this, apply kernel.of_mono, },
      rw ←to_single₀_cokernel_at_zero_iso_hom_eq,
      apply_instance }
end

lemma to_single₀_exact_at_succ [hf : quasi_iso f] (n : ℕ) :
  exact (X.d (n + 2) (n + 1)) (X.d (n + 1) n) :=
(preadditive.exact_iff_homology_zero _ _).2 ⟨X.d_comp_d _ _ _,
⟨(chain_complex.homology_succ_iso _ _).symm.trans
  ((@as_iso _ _ _ _ _ (hf.1 (n + 1))).trans homology_zero_zero)⟩⟩

end
section
variables {X : cochain_complex W ℕ} {Y : W}
  (f : (cochain_complex.single₀ _).obj Y ⟶ X)

/-- If a cochain map `f : Y[0] ⟶ X` is a quasi-isomorphism, then the kernel of the differential
`d : X₀ → X₁` is isomorphic to `Y.` -/
noncomputable def from_single₀_kernel_at_zero_iso [hf : quasi_iso f] : kernel (X.d 0 1) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (hf.1 0)).symm.trans
  ((cochain_complex.homology_functor_0_single₀ W).app Y)))

lemma from_single₀_kernel_at_zero_iso_inv_eq [hf : quasi_iso f] :
  f.from_single₀_kernel_at_zero_iso.inv = kernel.lift (X.d 0 1) (f.f 0)
    (by rw f.2 0 1 rfl; exact zero_comp) :=
begin
  ext,
  dunfold from_single₀_kernel_at_zero_iso cochain_complex.homology_zero_iso homology_of_zero_left
    homology.map_iso cochain_complex.homology_functor_0_single₀ kernel.map,
  simp only [iso.trans_inv, iso.app_inv, iso.symm_inv, category.assoc,
    equalizer_as_kernel, kernel.lift_ι],
  dsimp,
  simp only [category.assoc, homology.π_map, cokernel_zero_iso_target_hom,
    cokernel_iso_of_eq_hom_comp_desc, kernel_subobject_arrow, homology.π_map_assoc,
    is_iso.inv_comp_eq],
  simp [homology.π, kernel_subobject_map_comp, iso.refl_hom (X.X 0), category.comp_id],
end

lemma from_single₀_mono_at_zero [hf : quasi_iso f] :
  mono (f.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  rw [←kernel.lift_ι (X.d 0 1) (f.f 0) (by rw f.2 0 1 rfl; exact zero_comp),
    ←from_single₀_kernel_at_zero_iso_inv_eq] at Hgh,
  rw (@cancel_mono _ _ _ _ _ _ (mono_comp _ _) _ _).1 Hgh,
end

lemma from_single₀_exact_f_d_at_zero [hf : quasi_iso f] :
  exact (f.f 0) (X.d 0 1) :=
begin
  rw preadditive.exact_iff_homology_zero,
  have h : f.f 0 ≫ X.d 0 1 = 0,
  { simp only [homological_complex.hom.comm, cochain_complex.single₀_obj_X_d, zero_comp] },
  refine ⟨h, nonempty.intro (homology_iso_cokernel_lift _ _ _ ≪≫ _)⟩,
  { suffices : is_iso (kernel.lift (X.d 0 1) (f.f 0) h),
    { haveI := this, apply cokernel.of_epi },
    rw ←from_single₀_kernel_at_zero_iso_inv_eq f,
    apply_instance },
end

lemma from_single₀_exact_at_succ [hf : quasi_iso f] (n : ℕ) :
  exact (X.d n (n + 1)) (X.d (n + 1) (n + 2)) :=
(preadditive.exact_iff_homology_zero _ _).2
  ⟨X.d_comp_d _ _ _, ⟨(cochain_complex.homology_succ_iso _ _).symm.trans
  ((@as_iso _ _ _ _ _ (hf.1 (n + 1))).symm.trans homology_zero_zero)⟩⟩

end
end to_single₀
end homological_complex.hom

variables {A : Type*} [category A] [abelian A] {B : Type*} [category B] [abelian B]
  (F : A ⥤ B) [functor.additive F] [preserves_finite_limits F] [preserves_finite_colimits F]
  [faithful F]

lemma category_theory.functor.quasi_iso_of_map_quasi_iso
  {C D : homological_complex A c} (f : C ⟶ D)
  (hf : quasi_iso ((F.map_homological_complex _).map f)) : quasi_iso f :=
⟨λ i, begin
  haveI : is_iso (F.map ((homology_functor A c i).map f)),
  { rw [← functor.comp_map, ← nat_iso.naturality_2 (F.homology_functor_iso i) f,
      functor.comp_map],
    apply_instance, },
  exact is_iso_of_reflects_iso _ F,
end⟩
