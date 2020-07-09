/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

/-!
# The morphism from `image f` to `kernel g` when `f ≫ g = 0`

We define the map, as the lift of `image.ι f` to `kernel g`,
and check some basic properties:

* this map is a monomorphism
* given `A --0--> B --g--> C`, where `[mono g]`, this map is an epimorphism
* given `A --f--> B --0--> C`, where `[epi f]`, this map is an epimorphism

In later files, we define the homology of complex as the cokernel of this map,
and say a complex is exact at a point if this map is an epimorphism.
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

lemma image_to_kernel_map_zero_right {w} :
  image_to_kernel_map f (0 : B ⟶ C) w = image.ι f ≫ inv (kernel.ι (0 : B ⟶ C)) :=
begin
  ext,
  simp [image_to_kernel_map],
end

local attribute [instance] has_zero_object.has_zero

/--
`image_to_kernel_map` for `A --0--> B --g--> C`, where `[mono g]` is an epi
(i.e. the sequence is exact at `B`).
-/
lemma image_to_kernel_map_epi_of_zero_of_mono [mono g] [has_zero_object V] {w} :
  epi (image_to_kernel_map (0 : A ⟶ B) g w) :=
epi_of_target_iso_zero _ (kernel.of_mono g)

/--
`image_to_kernel_map` for `A --f--> B --0--> C`, where `[epi g]` is an epi
(i.e. the sequence is exact at `B`).
-/
lemma image_to_kernel_map_epi_of_epi_of_zero [epi f] {w} :
  epi (image_to_kernel_map f (0 : B ⟶ C) w) :=
begin
  simp only [image_to_kernel_map_zero_right],
  haveI := epi_image_of_epi f,
  apply epi_comp,
end

end category_theory
