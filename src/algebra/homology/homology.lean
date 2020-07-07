/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import algebra.homology.chain_complex
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

/-!
# (Co)homology groups for complexes

We setup that part of the theory of homology groups which works in
any category with kernels and images.

We define the homology groups themselves, and show that they induce maps on kernels.

Under the additional assumption that our category has equalizers and functorial images, we construct
induced morphisms on images and functorial induced morphisms in homology.

## Chains and cochains

Throughout we work with complexes graded by an arbitrary `[add_comm_group β]`,
with a differential with grading `b : β`.
Thus we're simultaneously doing homology and cohomology groups
(and in future enabling computing homologies for successive pages of spectral sequences?).

At the end of the file we set up abbreviations `cohomology` and `cohomology_functor`,
so that when you're working with a `C : cochain_complex V`, you can write `C.cohomology i`
rather than the confusing `C.homology i`.
-/

universes v u

open category_theory
open category_theory.limits

variables {V : Type u} [category.{v} V] [has_zero_morphisms V]

namespace category_theory

/-!
At this point we assume that we have all images, and all equalizers.
We need to assume all equalizers, not just kernels, so that
`factor_thru_image` is an epimorphism.
-/
variables [has_images V] [has_equalizers V]
variables {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

/--
The morphism from `image f` to `kernel g` when `f ≫ g = 0`.
-/
def image_to_kernel_map (w : f ≫ g = 0) :
  image f ⟶ kernel g :=
kernel.lift g (image.ι f) $ (cancel_epi (factor_thru_image f)).1 $ by simp [w]

instance image_to_kernel_map_mono {w : f ≫ g = 0} : mono (image_to_kernel_map f g w) :=
begin
  dsimp [image_to_kernel_map],
  apply_instance,
end

@[simp]
lemma image_to_kernel_map_zero_left [has_zero_object V] {w} :
  image_to_kernel_map (0 : A ⟶ B) g w = 0 :=
by simp [image_to_kernel_map]

@[simp]
lemma image_to_kernel_map_zero_right [has_zero_object V] {w} :
  image_to_kernel_map f (0 : B ⟶ C) w = image.ι f ≫ inv (kernel.ι (0 : B ⟶ C)) :=
begin
  ext,
  simp [image_to_kernel_map],
end

lemma image_to_kernel_map_epi_of_zero_of_mono [mono g] {w} :
  epi (image_to_kernel_map (0 : A ⟶ B) g w) :=
begin
  dsimp [image_to_kernel_map],
  sorry,
end

lemma image_to_kernel_map_epi_of_epi_of_zero [epi f] {w} :
  epi (image_to_kernel_map f (0 : B ⟶ C) w) :=
begin
  dsimp [image_to_kernel_map],
  sorry,
end

end category_theory

variables {β : Type} [add_comm_group β] {b : β}

namespace complex

section has_kernels

variable [has_kernels V]

/-- The map induced by a chain map between the kernels of the differentials. -/
def kernel_map {C C' : complex V b} (f : C ⟶ C') (i : β) :
  kernel (C.d i) ⟶ kernel (C'.d i) :=
kernel.lift _ (kernel.ι _ ≫ f.f i)
begin
  rw [category.assoc, ←complex.comm_at f, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp],
end

@[simp, reassoc]
lemma kernel_map_condition {C C' : complex V b} (f : C ⟶ C') (i : β) :
  kernel_map f i ≫ kernel.ι (C'.d i) = kernel.ι (C.d i) ≫ f.f i :=
by simp [kernel_map]

@[simp]
lemma kernel_map_id (C : complex V b) (i : β) :
  kernel_map (𝟙 C) i = 𝟙 _ :=
(cancel_mono (kernel.ι (C.d i))).1 $ by simp

@[simp]
lemma kernel_map_comp {C C' C'' : complex V b} (f : C ⟶ C')
  (g : C' ⟶ C'') (i : β) :
  kernel_map (f ≫ g) i = kernel_map f i ≫ kernel_map g i :=
(cancel_mono (kernel.ι (C''.d i))).1 $ by simp

/-- The kernels of the differentials of a cochain complex form a ℤ-graded object. -/
def kernel_functor : complex V b ⥤ graded_object β V :=
{ obj := λ C i, kernel (C.d i),
  map := λ X Y f i, kernel_map f i }

end has_kernels

section has_image_maps
variables [has_images V] [has_image_maps V]

/-- A morphism of cochain complexes induces a morphism on the images of the differentials in every
    degree. -/
abbreviation image_map {C C' : complex V b} (f : C ⟶ C') (i : β) :
  image (C.d i) ⟶ image (C'.d i) :=
image.map (arrow.hom_mk' (complex.comm_at f i).symm)

@[simp]
lemma image_map_ι {C C' : complex V b} (f : C ⟶ C') (i : β) :
  image_map f i ≫ image.ι (C'.d i) = image.ι (C.d i) ≫ f.f (i + b) :=
image.map_hom_mk'_ι (complex.comm_at f i).symm

end has_image_maps

variables [has_images V] [has_equalizers V]

/--
The connecting morphism from the image of `d i` to the kernel of `d (i ± 1)`.
-/
def image_to_kernel_map (C : complex V b) (i : β) :
  image (C.d i) ⟶ kernel (C.d (i+b)) :=
category_theory.image_to_kernel_map (C.d i) (C.d (i+b)) (by simp)

@[simp, reassoc]
lemma image_to_kernel_map_condition (C : complex V b) (i : β) :
  image_to_kernel_map C i ≫ kernel.ι (C.d (i + b)) = image.ι (C.d i) :=
by simp [image_to_kernel_map, category_theory.image_to_kernel_map]

@[reassoc]
lemma induced_maps_commute [has_image_maps V] {C C' : complex V b} (f : C ⟶ C')
  (i : β) :
  image_to_kernel_map C i ≫ kernel_map f (i + b) = image_map f i ≫ image_to_kernel_map C' i :=
by { ext, simp }

variables [has_cokernels V]

/-- The `i`-th homology group of the complex `C`. -/
def homology (C : complex V b) (i : β) : V :=
cokernel (image_to_kernel_map C (i-b))

variables [has_image_maps V]

/-- A morphism of complexes induces a morphism in homology at every degree. -/
def homology_map {C C' : complex V b} (f : C ⟶ C') (i : β) :
  C.homology i ⟶ C'.homology i :=
cokernel.desc _ (kernel_map f (i - b + b) ≫ cokernel.π _) $ by simp [induced_maps_commute_assoc]

@[simp, reassoc]
lemma homology_map_condition {C C' : complex V b} (f : C ⟶ C') (i : β) :
  cokernel.π (image_to_kernel_map C (i - b)) ≫ homology_map f i =
    kernel_map f (i - b + b) ≫ cokernel.π _ :=
by simp [homology_map]

@[simp]
lemma homology_map_id (C : complex V b) (i : β) :
  homology_map (𝟙 C) i = 𝟙 (homology C i) :=
begin
  ext,
  simp only [homology_map_condition, kernel_map_id, category.id_comp],
  erw [category.comp_id]
end

@[simp]
lemma homology_map_comp {C C' C'' : complex V b} (f : C ⟶ C') (g : C' ⟶ C'') (i : β) :
  homology_map (f ≫ g) i = homology_map f i ≫ homology_map g i :=
by { ext, simp }

variables (V)

/-- The homology functor from `β` graded complexes to `β` graded objects in `V`. -/
def homology_functor : complex V b ⥤ graded_object β V :=
{ obj := λ C i, homology C i,
  map := λ C C' f i, homology_map f i }

end complex

/-!
We now set up abbreviations so that you can write `C.cohomology i` or `(cohomology_functor V).map f`
when `C` is a cochain complex.
-/

namespace cochain_complex

variables [has_images V] [has_equalizers V] [has_cokernels V]

abbreviation cohomology (C : cochain_complex V) (i : ℤ) : V :=
complex.homology C i

variables [has_image_maps V]

abbreviation cohomology_map {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  C.cohomology i ⟶ C'.cohomology i :=
complex.homology_map f i

variables (V)

abbreviation cohomology_functor : cochain_complex V ⥤ graded_object ℤ V :=
complex.homology_functor V

end cochain_complex
