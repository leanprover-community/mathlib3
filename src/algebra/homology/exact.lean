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

This definition is equivalent to the homology at `B` vanishing (at least for preadditive
categories). At this level of generality, this is not necessarily equivalent to other reasonable
definitions of exactness, for example that the inclusion map `image.ι f` is a kernel of `g` or that
the map `image f ⟶ kernel g` is an isomorphism. By adding more assumptions on our category, we get
these equivalences and more. Currently, there is one particular set of assumptions mathlib knows
about: abelian categories. Consequently, many interesting results about exact sequences are found in
`category_theory/abelian/exact.lean`.

# Main results
* Suppose that cokernels exist and that `f` and `g` are exact. If `s` is any kernel fork over `g`
  and `t` is any cokernel cofork over `f`, then `fork.ι s ≫ cofork.π t = 0`.
* Precomposing the first morphism with an epimorphism retains exactness. Postcomposing the second
  morphism with a monomorphism retains exactness.
* If `f` and `g` are exact and `i` is an isomorphism, then `f ≫ i.hom` and `i.inv ≫ g` are also
  exact.

# Future work
* Short exact sequences, split exact sequences, the splitting lemma (maybe only for abelian
  categories?)
* Two adjacent maps in a chain complex are exact iff the homology vanishes

-/

universes v u

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]
variables [has_equalizers V] [has_images V]

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

lemma exact_comp_hom_inv_comp [exact f g] (i : B ≅ D) : exact (f ≫ i.hom) (i.inv ≫ g) :=
begin
  refine ⟨by simp, _⟩,
  rw image_to_kernel_map_comp_hom_inv_comp,
  haveI : epi (image_to_kernel_map f g exact.w ≫ (kernel_is_iso_comp i.inv g).inv) := epi_comp _ _,
  exact epi_comp _ _
end

lemma exact_comp_hom_inv_comp_iff (i : B ≅ D) : exact (f ≫ i.hom) (i.inv ≫ g) ↔ exact f g :=
begin
  refine ⟨_, by { introI, exact exact_comp_hom_inv_comp i }⟩,
  introI,
  have : exact ((f ≫ i.hom) ≫ i.inv) (i.hom ≫ i.inv ≫ g) := exact_comp_hom_inv_comp i.symm,
  simpa using this
end

lemma exact_epi_comp [exact g h] [epi f] : exact (f ≫ g) h :=
begin
  refine ⟨by simp, _⟩,
  rw image_to_kernel_map_comp_left,
  suffices : epi (image.pre_comp f g),
  { exactI epi_comp _ _ },
  apply epi_of_epi_fac (limits.image.factor_thru_image_pre_comp _ _),
  exact epi_comp _ _
end

lemma exact_comp_mono [exact f g] [mono h] : exact f (g ≫ h) :=
begin
  refine ⟨by simp, _⟩,
  letI : is_iso (kernel.lift (g ≫ h) (kernel.ι g) (by simp)) :=
    ⟨kernel.lift g (kernel.ι (g ≫ h)) (by simp [←cancel_mono h]), by tidy⟩,
  rw image_to_kernel_map_comp_right f g h exact.w,
  exact epi_comp _ _
end

lemma exact_kernel : exact (kernel.ι f) f :=
begin
  refine ⟨kernel.condition _, _⟩,
  letI : is_iso (image_to_kernel_map (kernel.ι f) f (kernel.condition f)) :=
    ⟨factor_thru_image (kernel.ι f),
      ⟨by simp [←cancel_mono (image.ι (kernel.ι f))], by tidy⟩⟩,
  apply_instance
end

section
variables (A)

lemma kernel_ι_eq_zero_of_exact_zero_left [exact (0 : A ⟶ B) g] : kernel.ι g = 0 :=
begin
  rw [←cancel_epi (image_to_kernel_map (0 : A ⟶ B) g exact.w),
    ←cancel_epi (factor_thru_image (0 : A ⟶ B))],
  simp
end

lemma exact_zero_left_of_mono [has_zero_object V] [mono g] : exact (0 : A ⟶ B) g :=
⟨by simp, image_to_kernel_map_epi_of_zero_of_mono _⟩

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
  zero_comp, comp_zero]

@[simp, reassoc] lemma fork_ι_comp_cofork_π [exact f g] (s : kernel_fork g)
  (t : cokernel_cofork f) : fork.ι s ≫ cofork.π t = 0 :=
comp_eq_zero_of_exact f g (kernel_fork.condition s) (cokernel_cofork.condition t)

end has_cokernels

section
local attribute [instance] has_zero_object.has_zero

lemma exact_of_zero [has_zero_object V] {A C : V} (f : A ⟶ 0) (g : 0 ⟶ C) : exact f g :=
begin
  obtain rfl : f = 0 := by ext,
  obtain rfl : g = 0 := by ext,
  fsplit,
  { simp, },
  { exact image_to_kernel_map_epi_of_zero_of_mono 0, },
end

end

end category_theory
