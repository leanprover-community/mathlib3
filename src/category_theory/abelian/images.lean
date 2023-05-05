/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.limits.shapes.kernels

/-!
# The abelian image and coimage.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In an abelian category we usually want the image of a morphism `f` to be defined as
`kernel (cokernel.π f)`, and the coimage to be defined as `cokernel (kernel.ι f)`.

We make these definitions here, as `abelian.image f` and `abelian.coimage f`
(without assuming the category is actually abelian),
and later relate these to the usual categorical notions when in an abelian category.

There is a canonical morphism `coimage_image_comparison : abelian.coimage f ⟶ abelian.image f`.
Later we show that this is always an isomorphism in an abelian category,
and conversely a category with (co)kernels and finite products in which this morphism
is always an isomorphism is an abelian category.
-/

noncomputable theory

universes v u

open category_theory
open category_theory.limits

namespace category_theory.abelian

variables {C : Type u} [category.{v} C] [has_zero_morphisms C] [has_kernels C] [has_cokernels C]
variables {P Q : C} (f : P ⟶ Q)

section image

/-- The kernel of the cokernel of `f` is called the (abelian) image of `f`. -/
protected abbreviation image : C := kernel (cokernel.π f)

/-- The inclusion of the image into the codomain. -/
protected abbreviation image.ι : abelian.image f ⟶ Q :=
kernel.ι (cokernel.π f)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
protected abbreviation factor_thru_image : P ⟶ abelian.image f :=
kernel.lift (cokernel.π f) f $ cokernel.condition f

/-- `f` factors through its image via the canonical morphism `p`. -/
@[simp, reassoc] protected lemma image.fac :
  abelian.factor_thru_image f ≫ image.ι f = f :=
kernel.lift_ι _ _ _

instance mono_factor_thru_image [mono f] : mono (abelian.factor_thru_image f) :=
mono_of_mono_fac $ image.fac f

end image

section coimage

/-- The cokernel of the kernel of `f` is called the (abelian) coimage of `f`. -/
protected abbreviation coimage : C := cokernel (kernel.ι f)

/-- The projection onto the coimage. -/
protected abbreviation coimage.π : P ⟶ abelian.coimage f :=
cokernel.π (kernel.ι f)

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
protected abbreviation factor_thru_coimage : abelian.coimage f ⟶ Q :=
cokernel.desc (kernel.ι f) f $ kernel.condition f

/-- `f` factors through its coimage via the canonical morphism `p`. -/
protected lemma coimage.fac : coimage.π f ≫ abelian.factor_thru_coimage f = f :=
cokernel.π_desc _ _ _

instance epi_factor_thru_coimage [epi f] : epi (abelian.factor_thru_coimage f) :=
epi_of_epi_fac $ coimage.fac f

end coimage

/--
The canonical map from the abelian coimage to the abelian image.
In any abelian category this is an isomorphism.

Conversely, any additive category with kernels and cokernels and
in which this is always an isomorphism, is abelian.

See <https://stacks.math.columbia.edu/tag/0107>
-/
def coimage_image_comparison : abelian.coimage f ⟶ abelian.image f :=
cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) $ (by { ext, simp, })

/--
An alternative formulation of the canonical map from the abelian coimage to the abelian image.
-/
def coimage_image_comparison' : abelian.coimage f ⟶ abelian.image f :=
kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by { ext, simp, })

lemma coimage_image_comparison_eq_coimage_image_comparison' :
  coimage_image_comparison f = coimage_image_comparison' f :=
by { ext, simp [coimage_image_comparison, coimage_image_comparison'], }

@[simp, reassoc]
lemma coimage_image_factorisation :
  coimage.π f ≫ coimage_image_comparison f ≫ image.ι f = f :=
by simp [coimage_image_comparison]

end category_theory.abelian
