/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.basic
import algebra.homology.exact
import tactic.tfae

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* `(f, g)` is exact if and only if `f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`. This
  characterisation tends to be less cumbersome to work with than the original definition involving
  the comparison map `image f ⟶ kernel g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π = 0` iff `exact f 0`.

-/

universes v u

noncomputable theory

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
      is_limit (kernel_fork.of_ι (image.ι f) (image_ι_comp_eq_zero h.1)),
    { have : image_to_kernel_map f g h.1 =
        (is_limit.cone_point_unique_up_to_iso hl (limit.is_limit _)).hom,
      { ext, simp },
      rw this,
      apply_instance },
    refine is_limit.of_ι _ _ _ _ _,
    { refine λ W u hu, kernel.lift (cokernel.π f) u _ ≫ (image_iso_image f).hom,
      rw [←kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero] },
    { tidy },
    { intros, simp [w, ←cancel_mono (image.ι f)] } }
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
    apply zero_of_comp_mono
      (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hf).hom,
    simp [h.2] }
end

/-- If `(f, g)` is exact, then `images.image.ι f` is a kernel of `g`. -/
def is_limit_image [h : exact f g] :
  is_limit
    (kernel_fork.of_ι (images.image.ι f) (images.image_ι_comp_eq_zero h.1) : kernel_fork g) :=
begin
  rw exact_iff at h,
  refine is_limit.of_ι _ _ _ _ _,
  { refine λ W u hu, kernel.lift (cokernel.π f) u _,
    rw [←kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero] },
  tidy
end

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def is_limit_image' [h : exact f g] :
  is_limit (kernel_fork.of_ι (image.ι f) (image_ι_comp_eq_zero h.1)) :=
is_kernel.iso_kernel _ _ (is_limit_image f g) (image_iso_image f).symm $ is_image.lift_fac _ _

lemma exact_cokernel : exact f (cokernel.π f) :=
by { rw exact_iff, tidy }

section
variables (Z)

lemma tfae_mono : tfae [mono f, kernel.ι f = 0, exact (0 : Z ⟶ X) f] :=
begin
  tfae_have : 3 → 2,
  { introsI, exact kernel_ι_eq_zero_of_exact_zero_left Z },
  tfae_have : 1 → 3,
  { introsI, exact exact_zero_left_of_mono Z },
  tfae_have : 2 → 1,
  { exact mono_of_kernel_ι_eq_zero _ },
  tfae_finish
end

lemma mono_iff_exact_zero_left : mono f ↔ exact (0 : Z ⟶ X) f :=
(tfae_mono Z f).out 0 2

lemma mono_iff_kernel_ι_eq_zero : mono f ↔ kernel.ι f = 0 :=
(tfae_mono X f).out 0 1

lemma tfae_epi : tfae [epi f, cokernel.π f = 0, exact f (0 : Y ⟶ Z)] :=
begin
  tfae_have : 3 → 2,
  { rw exact_iff,
    rintro ⟨-, h⟩,
    exact zero_of_epi_comp _ h },
  tfae_have : 1 → 3,
  { rw exact_iff,
    introI,
    exact ⟨by simp, by simp [cokernel.π_of_epi]⟩ },
  tfae_have : 2 → 1,
  { exact epi_of_cokernel_π_eq_zero _ },
  tfae_finish
end

lemma epi_iff_exact_zero_right : epi f ↔ exact f (0 : Y ⟶ Z) :=
(tfae_epi Z f).out 0 2

lemma epi_iff_cokernel_π_eq_zero : epi f ↔ cokernel.π f = 0 :=
(tfae_epi X f).out 0 1

end

end category_theory.abelian
