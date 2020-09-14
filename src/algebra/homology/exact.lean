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

(We say epimorphism rather than isomorphism because, at least for preadditive categories,
this is exactly equivalent to the homology at `i` vanishing.
In an abelian category, this is the same as asking for it to be an isomorphism,
because the inclusion map is always a monomorphism.)

# Main results
* Suppose that cokernels exist and that `f` and `g` are exact. If `s` is any kernel fork over `g`
  and `t` is any cokernel cofork over `f`, then `fork.ι s ≫ cofork.π t = 0`.

See also `category_theory/abelian/exact.lean` for results that only hold in abelian categories.

# Future work
* Short exact sequences, split exact sequences, the splitting lemma (maybe only for abelian
  categories?)
* Two adjacent maps in a chain complex are exact iff the homology vanishes
* Composing with isomorphisms retains exactness, and similar constructions

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

lemma exact.w_assoc {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} [exact f g] {h : C ⟶ D} :
  f ≫ g ≫ h = 0 :=
by rw [←category.assoc, @exact.w _ _ _ _ _ _ _ _ _ f g, zero_comp]

instance exact_comp_iso {A B C C' : V} (f : A ⟶ B) (g : B ⟶ C) (h : C ≅ C') [exact f g] :
  exact f (g ≫ h.hom) :=
{ w := exact.w_assoc,
  epi := by { simp only [image_to_kernel_map_comp_iso], apply epi_comp, } }

instance exact_iso_comp {A A' B C : V} (h : A' ≅ A) (f : A ⟶ B) (g : B ⟶ C) [exact f g] :
  exact (h.hom ≫ f) g :=
{ w := by rw [category.assoc, @exact.w _ _ _ _ _ _ _ _ _ f g, comp_zero],
  epi := by { simp only [image_to_kernel_map_iso_comp], apply epi_comp, } }

section
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

end

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
