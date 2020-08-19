/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.homology.image_to_kernel_map

/-!
# Exact sequences

In a category with zero morphisms, images, and equalizers we say that `f : A ⟶ B` and `g : B ⟶ C`
are exact if `f ≫ g = 0` and the natural map `image f ⟶ kernel g` is an epimorphism.

This is a relatively weak notion of exactness, and reasoning about exactness in this very general
setting is not very useful, for example because without further assumptions several "reasonable"
definitions of exactness are not equivalent. There are several nicer settings in which exact
sequences can be studied. At the moment, mathlib only knows one: abelian categories. Consequently,
many interesting results about exact sequences are found in `category_theory/abelian/exact.lean`.

# Main results
* Suppose that cokernels exist and that `f` and `g` are exact. If `s` is any kernel fork over `g`
  and `t` is any cokernel cofork over `f`, then `fork.ι s ≫ cofork.π t = 0`.

# Future work
* Short exact sequences, split exact sequences, the splitting lemma (maybe only for abelian
  categories?)
* Two adjacent maps in a chain complex are exact iff the homology vanishes

-/

universes v u

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
variables [has_kernels V] [has_equalizers V] [has_images V]

namespace category_theory

/-- Two morphisms `f : A ⟶ B`, `g : B ⟶ C` are called exact if `f ≫ g = 0` and the natural map
    `image f ⟶ kernel g` is an epimorphism. -/
class exact {A B C : V} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
(w : f ≫ g = 0)
(epi : epi (image_to_kernel_map f g w))

attribute [instance] exact.epi
attribute [simp, reassoc] exact.w

section
variables {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}

lemma exact_epi_comp [exact g h] [epi f] : exact (f ≫ g) h :=
begin
  refine ⟨by simp, _⟩,
  let mf : mono_factorisation (f ≫ g) :=
  { I := _,
    m := image.ι g,
    m_mono := by apply_instance,
    e := f ≫ factor_thru_image g,
    fac' := by simp },
  have : image_to_kernel_map (f ≫ g) h (by simp) = image.lift mf ≫ image_to_kernel_map g h exact.w,
  { ext, simp },
  rw this,
  suffices : epi (image.lift mf),
  { exactI epi_comp _ _ },
  haveI : epi (f ≫ factor_thru_image g) := epi_comp _ _,
  apply epi_of_epi_fac (image.fac_lift mf)
end

lemma exact_comp_mono [exact f g] [mono h] : exact f (g ≫ h) :=
begin
  refine ⟨by simp, _⟩,
  letI : is_iso (kernel.lift (g ≫ h) (kernel.ι g) (by simp)) :=
  { inv := kernel.lift g (kernel.ι (g ≫ h)) (by simp [←cancel_mono h]) },
  have : image_to_kernel_map f (g ≫ h) (by simp) = image_to_kernel_map f g exact.w ≫
    kernel.lift (g ≫ h) (kernel.ι g) (by simp),
  { ext, simp },
  rw this,
  exact epi_comp _ _
end

lemma exact_kernel : exact (kernel.ι f) f :=
begin
  refine ⟨kernel.condition _, _⟩,
  letI : is_iso (image_to_kernel_map (kernel.ι f) f (kernel.condition f)) :=
  { inv := factor_thru_image (kernel.ι f),
    hom_inv_id' := by simp [←cancel_mono (image.ι (kernel.ι f))] },
  apply_instance
end

lemma kernel_ι_eq_zero_of_exact_zero_left [exact (0 : A ⟶ B) g] : kernel.ι g = 0 :=
begin
  rw [←cancel_epi (image_to_kernel_map (0 : A ⟶ B) g exact.w),
    ←cancel_epi (factor_thru_image (0 : A ⟶ B))],
  simp
end

lemma exact_zero_left_of_mono [has_zero_object V] [mono g] : exact (0 : A ⟶ B) g :=
⟨by simp, image_to_kernel_map_epi_of_zero_of_mono _⟩

lemma exact_cokernel [has_cokernel f] : exact f (cokernel.π f) :=
begin

end

end

section has_cokernels
variables [has_cokernels V] {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp, reassoc] lemma kernel_comp_cokernel [exact f g] : kernel.ι g ≫ cokernel.π f = 0 :=
zero_of_epi_comp (image_to_kernel_map f g exact.w) $ zero_of_epi_comp (factor_thru_image f) $
  by simp

lemma comp_eq_zero_of_exact [exact f g] {X Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y}
  (hπ : f ≫ π = 0) : ι ≫ π = 0 :=
by rw [←kernel.lift_ι _ _ hι, ←cokernel.π_desc _ _ hπ, category.assoc, kernel_comp_cokernel_assoc,
  has_zero_morphisms.zero_comp, has_zero_morphisms.comp_zero]

@[simp, reassoc] lemma fork_ι_comp_cofork_π [exact f g] (s : kernel_fork g)
  (t : cokernel_cofork f) : fork.ι s ≫ cofork.π t = 0 :=
comp_eq_zero_of_exact f g (kernel_fork.condition s) (cokernel_cofork.condition t)

end has_cokernels

end category_theory
