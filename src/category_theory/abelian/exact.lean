/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.basic
import algebra.homology.exact

/-!
# Exact sequences in abelian categories

We prove that in an abelian category, `(f, g)` is exact if and only if `f ≫ g = 0` and
`kernel.ι g ≫ cokernel.π f = 0`.

-/

universes v u

open category_theory
open category_theory.limits
open category_theory.preadditive

variables {C : Type u} [category.{v} C] [abelian C]

namespace category_theory.abelian
variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

local attribute [instance] has_equalizers_of_has_kernels

theorem exact_iff : exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 :=
begin
  split,
  { introI h,
    exact ⟨h.1, kernel_comp_cokernel f g⟩ },
  { refine λ h, ⟨h.1, _⟩,
    suffices hl :
      is_limit (kernel_fork.of_ι (image.ι f) ((epi_iff_cancel_zero (factor_thru_image f)).1
        (by apply_instance) _ (image.ι f ≫ g) (by simp [h.1]))),
    { have : image_to_kernel_map f g h.1 =
        (is_limit.cone_point_unique_up_to_iso hl (limit.is_limit _)).hom,
      { ext, simp },
      rw this,
      apply_instance },
    refine is_limit.of_ι _ _ _ _ _,
    { refine λ W u hu, kernel.lift (cokernel.π f) u _,
      rw [←kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero] },
    { exact λ _ _ _, kernel.lift_ι _ _ _ },
    { tidy } }
end

theorem exact_iff' {cg : kernel_fork g} (hg : is_limit cg)
  {cf : cokernel_cofork f} (hf : is_colimit cf) : exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 :=
begin
  split,
  { introI h,
    exact ⟨h.1, fork_ι_comp_cofork_π f g cg cf⟩ },
  { rw exact_iff,
    refine λ h, ⟨h.1, _⟩,
    apply zero_of_epi_comp (is_limit.cone_point_unique_up_to_iso hg (limit.is_limit _)).hom,
    apply zero_of_comp_mono (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hf).hom,
    simp [h.2] }
end

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def is_limit_image [h : exact f g] : is_limit (kernel_fork.of_ι (image.ι f)
  ((epi_iff_cancel_zero (factor_thru_image f)).1 (by apply_instance) _ (image.ι f ≫ g)
  (by simp [h.1]))) :=
begin
  rw exact_iff at h,
  refine is_limit.of_ι _ _ _ _ _,
  { refine λ W u hu, kernel.lift (cokernel.π f) u _,
    rw [←kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero] },
  { exact λ _ _ _, kernel.lift_ι _ _ _ },
  { tidy }
end


end category_theory.abelian
