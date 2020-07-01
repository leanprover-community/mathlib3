/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import algebra.homology.chain_complex
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

/-!
# Cohomology groups for cochain complexes

We setup that part of the theory of cohomology groups which works in
any category with kernels and images.

We define the cohomology groups themselves, and show that they induce maps on kernels.

Under the additional assumption that our category has equalizers and functorial images, we construct
induced morphisms on images and functorial induced morphisms in cohomology.

-/

universes v u

namespace cochain_complex

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]

section

variable [has_kernels V]

/-- The map induced by a chain map between the kernels of the differentials. -/
def kernel_map {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  kernel (C.d i) ⟶ kernel (C'.d i) :=
kernel.lift _ (kernel.ι _ ≫ f.f i)
begin
  rw [category.assoc, ←comm_at f, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp],
end

@[simp, reassoc]
lemma kernel_map_condition {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  kernel_map f i ≫ kernel.ι (C'.d i) = kernel.ι (C.d i) ≫ f.f i :=
by simp [kernel_map]

@[simp]
lemma kernel_map_id (C : cochain_complex V) (i : ℤ) :
  kernel_map (𝟙 C) i = 𝟙 _ :=
(cancel_mono (kernel.ι (C.d i))).1 $ by simp

@[simp]
lemma kernel_map_comp {C C' C'' : cochain_complex V} (f : C ⟶ C')
  (g : C' ⟶ C'') (i : ℤ) :
  kernel_map (f ≫ g) i = kernel_map f i ≫ kernel_map g i :=
(cancel_mono (kernel.ι (C''.d i))).1 $ by simp

/-- The kernels of the differentials of a cochain complex form a ℤ-graded object. -/
def kernel_functor : cochain_complex V ⥤ graded_object ℤ V :=
{ obj := λ C i, kernel (C.d i),
  map := λ X Y f i, kernel_map f i }

end

section
variables [has_images V] [has_image_maps V]

/-- A morphism of cochain complexes induces a morphism on the images of the differentials in every
    degree. -/
abbreviation image_map {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  image (C.d i) ⟶ image (C'.d i) :=
image.map (arrow.hom_mk' (cochain_complex.comm_at f i).symm)

@[simp]
lemma image_map_ι {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  image_map f i ≫ image.ι (C'.d i) = image.ι (C.d i) ≫ f.f (i + 1) :=
image.map_hom_mk'_ι (cochain_complex.comm_at f i).symm

end

/-!
At this point we assume that we have all images, and all equalizers.
We need to assume all equalizers, not just kernels, so that
`factor_thru_image` is an epimorphism.
-/
variables [has_kernels V] [has_images V] [has_equalizers V]

/--
The connecting morphism from the image of `d i` to the kernel of `d (i+1)`.
-/
def image_to_kernel_map (C : cochain_complex V) (i : ℤ) :
  image (C.d i) ⟶ kernel (C.d (i+1)) :=
kernel.lift _ (image.ι (C.d i)) $ (cancel_epi (factor_thru_image (C.d i))).1 $ by simp

@[simp, reassoc]
lemma image_to_kernel_map_condition (C : cochain_complex V) (i : ℤ) :
  image_to_kernel_map C i ≫ kernel.ι (C.d (i + 1)) = image.ι (C.d i) :=
by simp [image_to_kernel_map]

@[reassoc]
lemma induced_maps_commute [has_image_maps V] {C C' : cochain_complex V} (f : C ⟶ C')
  (i : ℤ) :
  image_to_kernel_map C i ≫ kernel_map f (i + 1) = image_map f i ≫ image_to_kernel_map C' i :=
by { ext, simp }

variables [has_cokernels V]

/-- The `i`-th cohomology group of the cochain complex `C`. -/
def cohomology (C : cochain_complex V) (i : ℤ) : V :=
cokernel (image_to_kernel_map C (i-1))

variables [has_image_maps V]

/-- A morphism of cochain complexes induces a morphism in cohomology at every degree. -/
def cohomology_map {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  C.cohomology i ⟶ C'.cohomology i :=
cokernel.desc _ (kernel_map f (i - 1 + 1) ≫ cokernel.π _) $ by simp [induced_maps_commute_assoc]

@[simp, reassoc]
lemma cohomology_map_condition {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  cokernel.π (image_to_kernel_map C (i - 1)) ≫ cohomology_map f i =
    kernel_map f (i - 1 + 1) ≫ cokernel.π _ :=
by simp [cohomology_map]

@[simp]
lemma cohomology_map_id (C : cochain_complex V) (i : ℤ) :
  cohomology_map (𝟙 C) i = 𝟙 (cohomology C i) :=
begin
  ext,
  simp only [cohomology_map_condition, kernel_map_id, category.id_comp],
  erw [category.comp_id]
end

@[simp]
lemma cohomology_map_comp {C C' C'' : cochain_complex V} (f : C ⟶ C') (g : C' ⟶ C'') (i : ℤ) :
  cohomology_map (f ≫ g) i = cohomology_map f i ≫ cohomology_map g i :=
by { ext, simp }

/-- The cohomology functor from cochain complexes to `ℤ` graded objects in `V`. -/
def cohomology_functor : cochain_complex V ⥤ graded_object ℤ V :=
{ obj := λ C i, cohomology C i,
  map := λ C C' f i, cohomology_map f i }

end cochain_complex
