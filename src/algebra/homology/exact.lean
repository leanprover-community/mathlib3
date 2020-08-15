/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.homology.image_to_kernel_map

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

section
variables [has_cokernels V] {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp, reassoc] lemma kernel_comp_cokernel [exact f g] : kernel.ι g ≫ cokernel.π f = 0 :=
zero_of_epi_comp (image_to_kernel_map f g exact.w) $ zero_of_epi_comp (factor_thru_image f) $
  by simp

lemma bla [exact f g] {X Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y} (hπ : f ≫ π = 0) :
  ι ≫ π = 0 :=
by rw [←kernel.lift_ι _ _ hι, ←cokernel.π_desc _ _ hπ, category.assoc, kernel_comp_cokernel_assoc,
  has_zero_morphisms.zero_comp, has_zero_morphisms.comp_zero]

lemma bla' [exact f g] (s : kernel_fork g) (t : cokernel_cofork f) : fork.ι s ≫ cofork.π t = 0 :=
bla f g (kernel_fork.condition s) (cokernel_cofork.condition t)

end
end category_theory
