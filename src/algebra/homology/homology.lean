/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import algebra.homology.chain_complex
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

/-!
# Non-functorial cohomology groups for cochain complexes

We setup that part of the theory of cohomology groups which works in
any category with kernels and images.

We define the cohomology groups themselves, and while we can show that
chain maps induce maps on the kernels, at this level of generality
chain maps do not induce maps on the images, and so not on the cohomology groups.

We'll do this with stronger assumptions, later.
-/

universes v u

namespace cochain_complex

open category_theory
open category_theory.limits

variables {V : Type u} [𝒱 : category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

variable [has_kernels.{v} V]
/-- The map induced by a chain map between the kernels of the differentials. -/
def kernel_map {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  kernel (C.d i) ⟶ kernel (C'.d i) :=
kernel.lift _ (kernel.ι _ ≫ f.f i)
begin
  rw [category.assoc, ←comm_at f, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp],
end

@[simp]
lemma kernel_map_condition {C C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) :
  kernel_map f i ≫ kernel.ι (C'.d i) = kernel.ι (C.d i) ≫ f.f i :=
by erw [limit.lift_π, fork.of_ι_app_zero]

@[simp]
lemma kernel_map_id (C : cochain_complex.{v} V) (i : ℤ) :
  kernel_map (𝟙 C) i = 𝟙 _ :=
(cancel_mono (kernel.ι (C.d i))).1 $ by simp

@[simp]
lemma kernel_map_comp {C C' C'' : cochain_complex.{v} V} (f : C ⟶ C')
  (g : C' ⟶ C'') (i : ℤ) :
  kernel_map (f ≫ g) i = kernel_map f i ≫ kernel_map g i :=
(cancel_mono (kernel.ι (C''.d i))).1 $
  by rw [kernel_map_condition, category.assoc, kernel_map_condition,
    ←category.assoc, kernel_map_condition, category.assoc, differential_object.comp_f,
    graded_object.comp_apply]

-- TODO: Actually, this is a functor `cochain_complex V ⥤ cochain_complex V`, but to state this
-- properly we will need `has_shift` on `differential_object` first.
/-- The kernels of the differentials of a cochain complex form a ℤ-graded object. -/
def kernel_functor : cochain_complex.{v} V ⥤ graded_object ℤ V :=
{ obj := λ C i, kernel (C.d i),
  map := λ X Y f i, kernel_map f i }

/-!
At this point we assume that we have all images, and all equalizers.
We need to assume all equalizers, not just kernels, so that
`factor_thru_image` is an epimorphism.
-/
variables [has_images.{v} V] [has_equalizers.{v} V]

/--
The connecting morphism from the image of `d i` to the kernel of `d (i+1)`.
-/
def image_to_kernel_map (C : cochain_complex V) (i : ℤ) :
  image (C.d i) ⟶ kernel (C.d (i+1)) :=
kernel.lift _ (image.ι (C.d i))
begin
  rw ←cancel_epi (factor_thru_image (C.d i)),
  rw [has_zero_morphisms.comp_zero, image.fac_assoc, d_squared],
end

-- TODO (a good project!):
-- At this level of generality, it's just not true that a chain map
-- induces maps on boundaries
--
-- Let's add these later, with appropriate (but hopefully fairly minimal)
-- assumptions: perhaps that the category is regular?
-- I think in that case we can compute `image` as the regular coimage,
-- i.e. the coequalizer of the kernel pair,
-- and that image has the appropriate mapping property.

-- def image_map {C C' : cochain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   image (C.d i) ⟶ image (C'.d i) :=
-- sorry

-- -- I'm not certain what the minimal assumptions required to prove the following
-- -- lemma are:
-- lemma induced_maps_commute {C C' : cochain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
-- image_to_kernel_map C i ≫ kernel_map f (i+1) =
--   image_map f i ≫ image_to_kernel_map C' i :=
-- sorry

variables [has_cokernels.{v} V]

/-- The `i`-th cohomology group of the cochain complex `C`. -/
def cohomology (C : cochain_complex V) (i : ℤ) : V :=
cokernel (image_to_kernel_map C (i-1))

-- TODO:

-- As noted above, as we don't get induced maps on boundaries with this generality,
-- we can't assemble the cohomology groups into a functor. Hopefully, however,
-- the commented out code below will work
-- (with whatever added assumptions are needed above.)

-- def cohomology_map {C C' : cochain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   C.cohomology i ⟶ C'.cohomology i :=
-- cokernel.desc _ (kernel_map f (i-1) ≫ cokernel.π _)
-- begin
--   rw [←category.assoc, induced_maps_commute, category.assoc, cokernel.condition],
--   erw [has_zero_morphisms.comp_zero],
-- end

-- /-- The cohomology functor from chain complexes to `ℤ` graded objects in `V`. -/
-- def cohomology_functor : cochain_complex.{v} V ⥤ graded_object ℤ V :=
-- { obj := λ C i, cohomology C i,
--   map := λ C C' f i, cohomology_map f i,
--   map_id' := sorry,
--   map_comp' := sorry, }

end cochain_complex
