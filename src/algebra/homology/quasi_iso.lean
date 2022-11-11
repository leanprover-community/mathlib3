/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import algebra.homology.homology
import algebra.homology.homotopy
import category_theory.abelian.homology

/-!
# Quasi-isomorphisms

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

section to_single₀
variables {W : Type*} [category W] [abelian W]

section
variables {X : chain_complex W ℕ} {Y : W} (H : homotopy_equiv X ((chain_complex.single₀ _).obj Y))

/-- If a chain complex `X` is homotopy equivalent to a complex concentrated at 0 (for some
object `Y`), the cokernel of the differential `d : X₁ → X₀` is isomorphic to `Y.` -/
noncomputable def to_single₀_cokernel_at_zero : cokernel (X.d 1 0) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (H.to_quasi_iso.1 0)).trans
  ((chain_complex.homology_functor_0_single₀ W).app Y)))

lemma to_single₀_cokernel_at_zero_hom_eq :
  H.to_single₀_cokernel_at_zero.hom = cokernel.desc (X.d 1 0) (H.1.f 0)
    (by rw ←H.1.2 1 0 rfl; exact comp_zero) :=
begin
  ext,
  dunfold to_single₀_cokernel_at_zero chain_complex.homology_zero_iso homology_of_zero_right
    homology.map_iso chain_complex.homology_functor_0_single₀ cokernel.map,
  dsimp,
  simp only [cokernel.π_desc, category.assoc, homology.map_desc],
  simp only [←category.assoc, cokernel.π_desc],
  simp only [category.assoc, homology.desc, cokernel.π_desc],
  suffices : (iso.refl (X.X 0)).inv ≫ H.1.f 0 = H.1.f 0,
  begin
    by simpa,
  end,
  rw [iso.refl_inv, category.id_comp],
end

lemma to_single₀_f_0_epi :
  epi (H.hom.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  have : H.inv.f 0 ≫ H.hom.f 0 = 𝟙 _ := by rw [←homological_complex.comp_f, H.4.3 0]; simp,
  rw [←category.id_comp g, ←category.id_comp h, ←this,
    category.assoc, category.assoc, Hgh]
end

lemma to_single₀_exact_d_f_0 :
  exact (X.d 1 0) (H.hom.f 0) :=
begin
  rw preadditive.exact_iff_homology_zero,
  have h : X.d 1 0 ≫ H.hom.f 0 = 0,
  { simp only [← H.1.2 1 0 rfl, chain_complex.single₀_obj_X_d, comp_zero], },
  refine ⟨h, nonempty.intro (homology_iso_kernel_desc _ _ _ ≪≫ _)⟩,
  { suffices : is_iso (cokernel.desc _ _ h),
    { haveI := this, apply kernel.of_mono, },
      rw ←to_single₀_cokernel_at_zero_hom_eq,
      apply_instance }
end

lemma to_chain_complex_single₀_exact_succ (n : ℕ) :
  exact (X.d (n + 2) (n + 1)) (X.d (n + 1) n) :=
(preadditive.exact_iff_homology_zero _ _).2 ⟨X.d_comp_d _ _ _,
⟨(chain_complex.homology_succ_iso _ _).symm.trans
  ((homology_obj_iso_of_homotopy_equiv H _).trans homology_zero_zero)⟩⟩

end
section
variables {X : cochain_complex W ℕ} {Y : W}
  (H : homotopy_equiv X ((cochain_complex.single₀ _).obj Y))

/-- If a cochain complex `X` is homotopy equivalent to a complex concentrated at 0 (for some
object `Y`), the kernel of the differential `d : X₀ → X₁` is isomorphic to `Y.` -/
noncomputable def to_single₀_kernel_at_zero : kernel (X.d 0 1) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (H.to_quasi_iso.1 0)).trans
  ((cochain_complex.homology_functor_0_single₀ W).app Y)))

lemma to_single₀_kernel_at_zero_inv_eq :
  H.to_single₀_kernel_at_zero.inv = kernel.lift (X.d 0 1) (H.2.f 0)
    (by rw H.2.2 0 1 rfl; exact zero_comp) :=
begin
  ext,
  dunfold to_single₀_kernel_at_zero,
  simp only [iso.trans_inv, iso.app_inv, iso.symm_inv, category.assoc,
    equalizer_as_kernel, kernel.lift_ι, to_quasi_iso_inv],
  dunfold to_single₀_kernel_at_zero cochain_complex.homology_zero_iso homology_of_zero_left
    homology.map_iso cochain_complex.homology_functor_0_single₀ kernel.map,
  dsimp,
  simp only [category.assoc, homology.π_map, cokernel_zero_iso_target_hom,
    cokernel_iso_of_eq_hom_comp_desc, kernel_subobject_arrow, homology.π_map_assoc,
    is_iso.inv_comp_eq],
  rw [←category.assoc, ←category.assoc, ←kernel_subobject_map_comp, ←kernel_subobject_map_comp,
    ←category.assoc (homology.π _ _ _), homology.π],
  suffices : (kernel_subobject 0).arrow ≫ H.inv.f 0 ≫ (iso.refl (X.X 0)).hom
    = (kernel_subobject 0).arrow ≫ H.inv.f 0,
  begin
    simpa,
  end,
  rw [iso.refl_hom, category.comp_id],
end

lemma to_single₀_inv_f_0_mono :
  mono (H.inv.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  have : H.inv.f 0 ≫ H.hom.f 0 = 𝟙 _ := by rw [←homological_complex.comp_f, H.4.3 0]; simp,
    rw [←category.comp_id g, ←category.comp_id h, ←this,
    ←category.assoc, ←category.assoc, Hgh]
end

lemma to_single₀_exact_inv_f_d_0 :
  exact (H.inv.f 0) (X.d 0 1) :=
begin
  rw preadditive.exact_iff_homology_zero,
  have h : H.inv.f 0 ≫ X.d 0 1 = 0,
  { simp only [homological_complex.hom.comm, cochain_complex.single₀_obj_X_d, zero_comp] },
  refine ⟨h, nonempty.intro (homology_iso_cokernel_lift _ _ _ ≪≫ _)⟩,
  { suffices : is_iso (kernel.lift (X.d 0 1) (H.inv.f 0) h),
    { haveI := this, apply cokernel.of_epi },
    rw ←H.to_single₀_kernel_at_zero_inv_eq,
    apply_instance },
end

lemma to_cochain_complex_single₀_exact_succ (n : ℕ) :
  exact (X.d n (n + 1)) (X.d (n + 1) (n + 2)) :=
(preadditive.exact_iff_homology_zero _ _).2
  ⟨X.d_comp_d _ _ _, ⟨(cochain_complex.homology_succ_iso _ _).symm.trans
  ((homology_obj_iso_of_homotopy_equiv H _).trans homology_zero_zero)⟩⟩

end
end to_single₀
end homotopy_equiv
