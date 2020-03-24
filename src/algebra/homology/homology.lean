/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.chain_complex
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

/-!
# Non-functorial homology groups for chain complexes

We setup that part of the theory of homology groups which works in
any category with kernels and images.

We define the homology groups themselves, and while we can show that
chain maps induce maps on the kernels, at this level of generality
chain maps do not induce maps on the images, and so not on the homology groups.

We'll do this with stronger assumptions, later.
-/

universes v u

namespace chain_complex

open category_theory
open category_theory.limits

variables {V : Type u} [𝒱 : category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

variable [has_kernels.{v} V]
/-- The map induceed by a chain map between the kernels of the differentials. -/
def induced_map_on_cycles {C C' : chain_complex V} (f : C ⟶ C') (i : ℤ) :
  kernel (C.d i) ⟶ kernel (C'.d i) :=
kernel.lift _ (kernel.ι _ ≫ f.f i)
begin
  rw [category.assoc, ←comm_at f, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp],
end

/-!
At this point we assume that we have all images, and all equalizers.
We need to assume all equalizers, not just kernels, so that
`factor_thru_image` is an epimorphism.
-/
variables [has_images.{v} V] [has_equalizers.{v} V]

/--
The connecting morphism from the image of `d i` to the kernel of `d (i+1)`.
-/
def image_to_kernel_map (C : chain_complex V) (i : ℤ) :
  image (C.d i) ⟶ kernel (C.d (i+1)) :=
kernel.lift _ (image.ι (C.d i))
begin
  rw ←cancel_epi (factor_thru_image (C.d i)),
  rw [has_zero_morphisms.comp_zero, image.fac_assoc, d_squared],
  refl,
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

-- def induced_map_on_boundaries {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   image (C.d i) ⟶ image (C'.d i) :=
-- sorry

-- -- I'm not certain what the minimal assumptions required to prove the following
-- -- lemma are:
-- lemma induced_maps_commute {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
-- image_to_kernel_map C i ≫ induced_map_on_cycles f (i+1) =
--   induced_map_on_boundaries f i ≫ image_to_kernel_map C' i :=
-- sorry

variables [has_cokernels.{v} V]

/-- The `i`-th homology group of the chain complex `C`. -/
def homology (C : chain_complex V) (i : ℤ) : V :=
cokernel (image_to_kernel_map C (i-1))

-- TODO:

-- As noted above, as we don't get induced maps on boundaries with this generality,
-- we can't assemble the homology groups into a functor. Hopefully, however,
-- the commented out code below will work
-- (with whatever added assumptions are needed above.)

-- def induced_map_on_homology {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   C.homology i ⟶ C'.homology i :=
-- cokernel.desc _ (induced_map_on_cycles f (i-1) ≫ cokernel.π _)
-- begin
--   rw [←category.assoc, induced_maps_commute, category.assoc, cokernel.condition],
--   erw [has_zero_morphisms.comp_zero],
-- end

-- /-- The homology functor from chain complexes to `ℤ` graded objects in `V`. -/
-- def homology_functor : chain_complex.{v} V ⥤ graded_object ℤ V :=
-- { obj := λ C i, homology C i,
--   map := λ C C' f i, induced_map_on_homology f i,
--   map_id' := sorry,
--   map_comp' := sorry, }

end chain_complex
