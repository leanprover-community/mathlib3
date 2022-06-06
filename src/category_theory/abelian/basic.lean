/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Johan Commelin, Scott Morrison
-/

import category_theory.limits.constructions.pullbacks
import category_theory.limits.shapes.biproducts
import category_theory.limits.shapes.images
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.limits.constructions.epi_mono
import category_theory.abelian.non_preadditive

/-!
# Abelian categories

This file contains the definition and basic properties of abelian categories.

There are many definitions of abelian category. Our definition is as follows:
A category is called abelian if it is preadditive,
has a finite products, kernels and cokernels,
and if every monomorphism and epimorphism is normal.

It should be noted that if we also assume coproducts, then preadditivity is
actually a consequence of the other properties, as we show in
`non_preadditive_abelian.lean`. However, this fact is of little practical
relevance, since essentially all interesting abelian categories come with a
preadditive structure. In this way, by requiring preadditivity, we allow the
user to pass in the "native" preadditive structure for the specific category they are
working with.

## Main definitions

* `abelian` is the type class indicating that a category is abelian. It extends `preadditive`.
* `abelian.image f` is `kernel (cokernel.π f)`, and
* `abelian.coimage f` is `cokernel (kernel.ι f)`.

## Main results

* In an abelian category, mono + epi = iso.
* If `f : X ⟶ Y`, then the map `factor_thru_image f : X ⟶ image f` is an epimorphism, and the map
  `factor_thru_coimage f : coimage f ⟶ Y` is a monomorphism.
* Factoring through the image and coimage is a strong epi-mono factorisation. This means that
  * every abelian category has images. We provide the isomorphism
    `image_iso_image : abelian.image f ≅ limits.image f`.
  * the canonical morphism `coimage_image_comparison : coimage f ⟶ image f`
    is an isomorphism.
* We provide the alternate characterisation of an abelian category as a category with
  (co)kernels and finite products, and in which the canonical coimage-image comparison morphism
  is always an isomorphism.
* Every epimorphism is a cokernel of its kernel. Every monomorphism is a kernel of its cokernel.
* The pullback of an epimorphism is an epimorphism. The pushout of a monomorphism is a monomorphism.
  (This is not to be confused with the fact that the pullback of a monomorphism is a monomorphism,
  which is true in any category).

## Implementation notes

The typeclass `abelian` does not extend `non_preadditive_abelian`,
to avoid having to deal with comparing the two `has_zero_morphisms` instances
(one from `preadditive` in `abelian`, and the other a field of `non_preadditive_abelian`).
As a consequence, at the beginning of this file we trivially build
a `non_preadditive_abelian` instance from an `abelian` instance,
and use this to restate a number of theorems,
in each case just reusing the proof from `non_preadditive_abelian.lean`.

We don't show this yet, but abelian categories are finitely complete and finitely cocomplete.
However, the limits we can construct at this level of generality will most likely be less nice than
the ones that can be created in specific applications. For this reason, we adopt the following
convention:

* If the statement of a theorem involves limits, the existence of these limits should be made an
  explicit typeclass parameter.
* If a limit only appears in a proof, but not in the statement of a theorem, the limit should not
  be a typeclass parameter, but instead be created using `abelian.has_pullbacks` or a similar
  definition.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
* [P. Aluffi, *Algebra: Chapter 0*][aluffi2016]

-/

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C]

variables (C)

/--
A (preadditive) category `C` is called abelian if it has all finite products,
all kernels and cokernels, and if every monomorphism is the kernel of some morphism
and every epimorphism is the cokernel of some morphism.

(This definition implies the existence of zero objects:
finite products give a terminal object, and in a preadditive category
any terminal object is a zero object.)
-/
class abelian extends preadditive C, normal_mono_category C, normal_epi_category C :=
[has_finite_products : has_finite_products C]
[has_kernels : has_kernels C]
[has_cokernels : has_cokernels C]

attribute [instance, priority 100] abelian.has_finite_products
attribute [instance, priority 100] abelian.has_kernels abelian.has_cokernels

end category_theory

open category_theory

/-!
We begin by providing an alternative constructor:
a preadditive category with kernels, cokernels, and finite products,
in which the coimage-image comparison morphism is always an isomorphism,
is an abelian category.
-/
namespace category_theory.abelian

variables {C : Type u} [category.{v} C] [preadditive C]
variables [limits.has_kernels C] [limits.has_cokernels C]

namespace of_coimage_image_comparison_is_iso

/-- The factorisation of a morphism through its abelian image. -/
@[simps]
def image_mono_factorisation {X Y : C} (f : X ⟶ Y) : mono_factorisation f :=
{ I := abelian.image f,
  m := kernel.ι _,
  m_mono := infer_instance,
  e := kernel.lift _ f (cokernel.condition _),
  fac' := kernel.lift_ι _ _ _ }

lemma image_mono_factorisation_e' {X Y : C} (f : X ⟶ Y) :
  (image_mono_factorisation f).e = cokernel.π _ ≫ abelian.coimage_image_comparison f :=
begin
  ext,
  simp only [abelian.coimage_image_comparison, image_mono_factorisation_e,
    category.assoc, cokernel.π_desc_assoc],
end

/-- If the coimage-image comparison morphism for a morphism `f` is an isomorphism,
we obtain an image factorisation of `f`. -/
def image_factorisation {X Y : C} (f : X ⟶ Y) [is_iso (abelian.coimage_image_comparison f)] :
  image_factorisation f :=
{ F := image_mono_factorisation f,
  is_image :=
  { lift := λ F, inv (abelian.coimage_image_comparison f) ≫ cokernel.desc _ F.e F.kernel_ι_comp,
    lift_fac' := λ F, begin
      simp only [image_mono_factorisation_m, is_iso.inv_comp_eq, category.assoc,
        abelian.coimage_image_comparison],
      ext,
      rw [limits.coequalizer.π_desc_assoc, limits.coequalizer.π_desc_assoc, F.fac, kernel.lift_ι]
    end } }

instance [has_zero_object C] {X Y : C} (f : X ⟶ Y) [mono f]
  [is_iso (abelian.coimage_image_comparison f)] :
  is_iso (image_mono_factorisation f).e :=
by { rw image_mono_factorisation_e', exact is_iso.comp_is_iso }

instance [has_zero_object C] {X Y : C} (f : X ⟶ Y) [epi f] :
  is_iso (image_mono_factorisation f).m :=
by { dsimp, apply_instance }

variables [∀ {X Y : C} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f)]

/-- A category in which coimage-image comparisons are all isomorphisms has images. -/
lemma has_images : has_images C :=
{ has_image := λ X Y f,
  { exists_image := ⟨image_factorisation f⟩ } }

variables [limits.has_finite_products C]
local attribute [instance] limits.has_finite_biproducts.of_has_finite_products

/--
A category with finite products in which coimage-image comparisons are all isomorphisms
is a normal mono category.
-/
def normal_mono_category : normal_mono_category C :=
{ normal_mono_of_mono := λ X Y f m,
  { Z := _,
    g := cokernel.π f,
    w := by simp,
    is_limit := begin
      haveI : limits.has_images C := has_images,
      haveI : has_equalizers C := preadditive.has_equalizers_of_has_kernels,
      haveI : has_zero_object C := limits.has_zero_object_of_has_finite_biproducts _,
      have aux : _ := _,
      refine is_limit_aux _ (λ A, limit.lift _ _ ≫ inv (image_mono_factorisation f).e) aux _,
      { intros A g hg,
        rw [kernel_fork.ι_of_ι] at hg,
        rw [← cancel_mono f, hg, ← aux, kernel_fork.ι_of_ι], },
      { intro A,
        simp only [kernel_fork.ι_of_ι, category.assoc],
        convert limit.lift_π _ _ using 2,
        rw [is_iso.inv_comp_eq, eq_comm],
        exact (image_mono_factorisation f).fac, },
    end }, }

/--
A category with finite products in which coimage-image comparisons are all isomorphisms
is a normal epi category.
-/
def normal_epi_category : normal_epi_category C :=
{ normal_epi_of_epi := λ X Y f m,
  { W := kernel f,
    g := kernel.ι _,
    w := kernel.condition _,
    is_colimit := begin
      haveI : limits.has_images C := has_images,
      haveI : has_equalizers C := preadditive.has_equalizers_of_has_kernels,
      haveI : has_zero_object C := limits.has_zero_object_of_has_finite_biproducts _,
      have aux : _ := _,
      refine is_colimit_aux _
        (λ A, inv (image_mono_factorisation f).m ≫
          inv (abelian.coimage_image_comparison f) ≫ colimit.desc _ _)
        aux _,
      { intros A g hg,
        rw [cokernel_cofork.π_of_π] at hg,
        rw [← cancel_epi f, hg, ← aux, cokernel_cofork.π_of_π], },
      { intro A,
        simp only [cokernel_cofork.π_of_π, ← category.assoc],
        convert colimit.ι_desc _ _ using 2,
        rw [is_iso.comp_inv_eq, is_iso.comp_inv_eq, eq_comm, ←image_mono_factorisation_e'],
        exact (image_mono_factorisation f).fac, }
    end }, }

end of_coimage_image_comparison_is_iso

variables [∀ {X Y : C} (f : X ⟶ Y), is_iso (abelian.coimage_image_comparison f)]
  [limits.has_finite_products C]
local attribute [instance] of_coimage_image_comparison_is_iso.normal_mono_category
local attribute [instance] of_coimage_image_comparison_is_iso.normal_epi_category

/--
A preadditive category with kernels, cokernels, and finite products,
in which the coimage-image comparison morphism is always an isomorphism,
is an abelian category.

The Stacks project uses this characterisation at the definition of an abelian category.
See <https://stacks.math.columbia.edu/tag/0109>.
-/
def of_coimage_image_comparison_is_iso : abelian C := {}

end category_theory.abelian

namespace category_theory.abelian
variables {C : Type u} [category.{v} C] [abelian C]

/-- An abelian category has finite biproducts. -/
@[priority 100]
instance has_finite_biproducts : has_finite_biproducts C :=
limits.has_finite_biproducts.of_has_finite_products

@[priority 100]
instance has_binary_biproducts : has_binary_biproducts C :=
limits.has_binary_biproducts_of_finite_biproducts _

@[priority 100]
instance has_zero_object : has_zero_object C :=
has_zero_object_of_has_initial_object

section to_non_preadditive_abelian

/-- Every abelian category is, in particular, `non_preadditive_abelian`. -/
def non_preadditive_abelian : non_preadditive_abelian C := { ..‹abelian C› }

end to_non_preadditive_abelian

section
/-! We now promote some instances that were constructed using `non_preadditive_abelian`. -/

local attribute [instance] non_preadditive_abelian

variables {P Q : C} (f : P ⟶ Q)

/-- The map `p : P ⟶ image f` is an epimorphism -/
instance : epi (abelian.factor_thru_image f) := by apply_instance

instance is_iso_factor_thru_image [mono f] : is_iso (abelian.factor_thru_image f) :=
by apply_instance

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance : mono (abelian.factor_thru_coimage f) := by apply_instance

instance is_iso_factor_thru_coimage [epi f] : is_iso (abelian.factor_thru_coimage f) :=
by apply_instance

end

section factor
local attribute [instance] non_preadditive_abelian

variables {P Q : C} (f : P ⟶ Q)

section

lemma mono_of_kernel_ι_eq_zero (h : kernel.ι f = 0) : mono f :=
mono_of_kernel_zero h

lemma epi_of_cokernel_π_eq_zero (h : cokernel.π f = 0) : epi f :=
begin
  apply normal_mono_category.epi_of_zero_cokernel _ (cokernel f),
  simp_rw ←h,
  exact is_colimit.of_iso_colimit (colimit.is_colimit (parallel_pair f 0)) (iso_of_π _)
end

end

section
variables {f}

lemma image_ι_comp_eq_zero {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : abelian.image.ι f ≫ g = 0 :=
zero_of_epi_comp (abelian.factor_thru_image f) $ by simp [h]

lemma comp_coimage_π_eq_zero {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : f ≫ abelian.coimage.π g = 0 :=
zero_of_comp_mono (abelian.factor_thru_coimage g) $ by simp [h]

end

/-- Factoring through the image is a strong epi-mono factorisation. -/
@[simps] def image_strong_epi_mono_factorisation : strong_epi_mono_factorisation f :=
{ I := abelian.image f,
  m := image.ι f,
  m_mono := by apply_instance,
  e := abelian.factor_thru_image f,
  e_strong_epi := strong_epi_of_epi _ }

/-- Factoring through the coimage is a strong epi-mono factorisation. -/
@[simps] def coimage_strong_epi_mono_factorisation : strong_epi_mono_factorisation f :=
{ I := abelian.coimage f,
  m := abelian.factor_thru_coimage f,
  m_mono := by apply_instance,
  e := coimage.π f,
  e_strong_epi := strong_epi_of_epi _ }

end factor

section has_strong_epi_mono_factorisations

/-- An abelian category has strong epi-mono factorisations. -/
@[priority 100] instance : has_strong_epi_mono_factorisations C :=
has_strong_epi_mono_factorisations.mk $ λ X Y f, image_strong_epi_mono_factorisation f

/- In particular, this means that it has well-behaved images. -/
example : has_images C := by apply_instance
example : has_image_maps C := by apply_instance

end has_strong_epi_mono_factorisations

section images
variables {X Y : C} (f : X ⟶ Y)

/--
The coimage-image comparison morphism is always an isomorphism in an abelian category.
See `category_theory.abelian.of_coimage_image_comparison_is_iso` for the converse.
-/
instance : is_iso (coimage_image_comparison f) :=
begin
  convert is_iso.of_iso (is_image.iso_ext (coimage_strong_epi_mono_factorisation f).to_mono_is_image
    (image_strong_epi_mono_factorisation f).to_mono_is_image),
  ext,
  change _ = _ ≫ (image_strong_epi_mono_factorisation f).m,
  simp [-image_strong_epi_mono_factorisation_to_mono_factorisation_m]
end

/-- There is a canonical isomorphism between the abelian coimage and the abelian image of a
    morphism. -/
abbreviation coimage_iso_image : abelian.coimage f ≅ abelian.image f :=
as_iso (coimage_image_comparison f)

/-- There is a canonical isomorphism between the abelian coimage and the categorical image of a
    morphism. -/
abbreviation coimage_iso_image' : abelian.coimage f ≅ image f :=
is_image.iso_ext (coimage_strong_epi_mono_factorisation f).to_mono_is_image
  (image.is_image f)

/-- There is a canonical isomorphism between the abelian image and the categorical image of a
    morphism. -/
abbreviation image_iso_image : abelian.image f ≅ image f :=
is_image.iso_ext (image_strong_epi_mono_factorisation f).to_mono_is_image (image.is_image f)

namespace preserves_image

variables {𝓐 𝓑 : Type u} [category.{v} 𝓐] [category.{v} 𝓑]
variables [abelian 𝓐] [abelian 𝓑]
variables (L : 𝓐 ⥤ 𝓑) [preserves_finite_limits L] [preserves_finite_colimits L]

/-
If a functor preserves both finite limits and colimits, then it preserves images.
-/
def iso {X Y : 𝓐} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
have aux1 : strong_epi_mono_factorisation (L.map f) :=
{ I := L.obj (limits.image f),
  m := L.map $ limits.image.ι _,
  m_mono := by apply_instance,
  e := L.map $ factor_thru_image _,
  e_strong_epi := strong_epi_of_epi _,
  fac' := by rw [←L.map_comp, limits.image.fac] },
is_image.iso_ext (image.is_image (L.map f)) aux1.to_mono_is_image

lemma precomp_factor_thru_image {X Y : 𝓐} (f : X ⟶ Y) :
  factor_thru_image  (L.map f) ≫ (iso L f).hom =
  L.map (factor_thru_image f) :=
begin
  dunfold iso,
  simp only [is_image.iso_ext_hom],
  erw image.fac_lift,
end

end preserves_image

end images

section cokernel_of_kernel
variables {X Y : C} {f : X ⟶ Y}

local attribute [instance] non_preadditive_abelian

/-- In an abelian category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel [epi f] (s : fork f 0) (h : is_limit s) :
  is_colimit (cokernel_cofork.of_π f (kernel_fork.condition s)) :=
non_preadditive_abelian.epi_is_cokernel_of_kernel s h

/-- In an abelian category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def mono_is_kernel_of_cokernel [mono f] (s : cofork f 0) (h : is_colimit s) :
  is_limit (kernel_fork.of_ι f (cokernel_cofork.condition s)) :=
non_preadditive_abelian.mono_is_kernel_of_cokernel s h

variables (f)

/-- In an abelian category, any morphism that turns to zero when precomposed with the kernel of an
    epimorphism factors through that epimorphism. -/
def epi_desc [epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) : Y ⟶ T :=
(epi_is_cokernel_of_kernel _ (limit.is_limit _)).desc (cokernel_cofork.of_π _ hg)

@[simp, reassoc]
lemma comp_epi_desc [epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) :
  f ≫ epi_desc f g hg = g :=
(epi_is_cokernel_of_kernel _ (limit.is_limit _)).fac (cokernel_cofork.of_π _ hg)
  walking_parallel_pair.one

/-- In an abelian category, any morphism that turns to zero when postcomposed with the cokernel of a
    monomorphism factors through that monomorphism. -/
def mono_lift [mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) : T ⟶ X :=
(mono_is_kernel_of_cokernel _ (colimit.is_colimit _)).lift (kernel_fork.of_ι _ hg)

@[simp, reassoc]
lemma mono_lift_comp [mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) :
  mono_lift f g hg ≫ f = g :=
(mono_is_kernel_of_cokernel _ (colimit.is_colimit _)).fac (kernel_fork.of_ι _ hg)
  walking_parallel_pair.zero

end cokernel_of_kernel

section

@[priority 100]
instance has_equalizers : has_equalizers C :=
preadditive.has_equalizers_of_has_kernels

/-- Any abelian category has pullbacks -/
@[priority 100]
instance has_pullbacks : has_pullbacks C :=
has_pullbacks_of_has_binary_products_of_has_equalizers C

end

section

@[priority 100]
instance has_coequalizers : has_coequalizers C :=
preadditive.has_coequalizers_of_has_cokernels

/-- Any abelian category has pushouts -/
@[priority 100]
instance has_pushouts : has_pushouts C :=
has_pushouts_of_has_binary_coproducts_of_has_coequalizers C

@[priority 100]
instance has_finite_limits : has_finite_limits C :=
limits.finite_limits_from_equalizers_and_finite_products

@[priority 100]
instance has_finite_colimits : has_finite_colimits C :=
limits.finite_colimits_from_coequalizers_and_finite_coproducts

end

namespace pullback_to_biproduct_is_kernel
variables [limits.has_pullbacks C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-! This section contains a slightly technical result about pullbacks and biproducts.
    We will need it in the proof that the pullback of an epimorphism is an epimorpism. -/

/-- The canonical map `pullback f g ⟶ X ⊞ Y` -/
abbreviation pullback_to_biproduct : pullback f g ⟶ X ⊞ Y :=
biprod.lift pullback.fst pullback.snd

/-- The canonical map `pullback f g ⟶ X ⊞ Y` induces a kernel cone on the map
    `biproduct X Y ⟶ Z` induced by `f` and `g`. A slightly more intuitive way to think of
    this may be that it induces an equalizer fork on the maps induced by `(f, 0)` and
    `(0, g)`. -/
abbreviation pullback_to_biproduct_fork : kernel_fork (biprod.desc f (-g)) :=
kernel_fork.of_ι (pullback_to_biproduct f g) $
by rw [biprod.lift_desc, comp_neg, pullback.condition, add_right_neg]

/-- The canonical map `pullback f g ⟶ X ⊞ Y` is a kernel of the map induced by
    `(f, -g)`. -/
def is_limit_pullback_to_biproduct : is_limit (pullback_to_biproduct_fork f g) :=
fork.is_limit.mk _
  (λ s, pullback.lift (fork.ι s ≫ biprod.fst) (fork.ι s ≫ biprod.snd) $
    sub_eq_zero.1 $ by rw [category.assoc, category.assoc, ←comp_sub, sub_eq_add_neg, ←comp_neg,
      ←biprod.desc_eq, kernel_fork.condition s])
  (λ s,
  begin
    ext; rw [fork.ι_of_ι, category.assoc],
    { rw [biprod.lift_fst, pullback.lift_fst] },
    { rw [biprod.lift_snd, pullback.lift_snd] }
  end)
  (λ s m h, by ext; simp [←h])

end pullback_to_biproduct_is_kernel

namespace biproduct_to_pushout_is_cokernel
variables [limits.has_pushouts C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

/-- The canonical map `Y ⊞ Z ⟶ pushout f g` -/
abbreviation biproduct_to_pushout : Y ⊞ Z ⟶ pushout f g :=
biprod.desc pushout.inl pushout.inr

/-- The canonical map `Y ⊞ Z ⟶ pushout f g` induces a cokernel cofork on the map
    `X ⟶ Y ⊞ Z` induced by `f` and `-g`. -/
abbreviation biproduct_to_pushout_cofork : cokernel_cofork (biprod.lift f (-g)) :=
cokernel_cofork.of_π (biproduct_to_pushout f g) $
by rw [biprod.lift_desc, neg_comp, pushout.condition, add_right_neg]

/-- The cofork induced by the canonical map `Y ⊞ Z ⟶ pushout f g` is in fact a colimit cokernel
    cofork. -/
def is_colimit_biproduct_to_pushout : is_colimit (biproduct_to_pushout_cofork f g) :=
cofork.is_colimit.mk _
  (λ s, pushout.desc (biprod.inl ≫ cofork.π s) (biprod.inr ≫ cofork.π s) $
    sub_eq_zero.1 $ by rw [←category.assoc, ←category.assoc, ←sub_comp, sub_eq_add_neg, ←neg_comp,
      ←biprod.lift_eq, cofork.condition s, zero_comp])
  (λ s, by ext; simp)
  (λ s m h, by ext; simp [←h] )

end biproduct_to_pushout_is_cokernel

section epi_pullback
variables [limits.has_pullbacks C] {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- In an abelian category, the pullback of an epimorphism is an epimorphism.
    Proof from [aluffi2016, IX.2.3], cf. [borceux-vol2, 1.7.6] -/
instance epi_pullback_of_epi_f [epi f] : epi (pullback.snd : pullback f g ⟶ Y) :=
-- It will suffice to consider some morphism e : Y ⟶ R such that
-- pullback.snd ≫ e = 0 and show that e = 0.
epi_of_cancel_zero _ $ λ R e h,
begin
  -- Consider the morphism u := (0, e) : X ⊞ Y⟶ R.
  let u := biprod.desc (0 : X ⟶ R) e,
  -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
  have hu : pullback_to_biproduct_is_kernel.pullback_to_biproduct f g ≫ u = 0 := by simpa,
  -- pullback_to_biproduct f g is a kernel of (f, -g), so (f, -g) is a
  -- cokernel of pullback_to_biproduct f g
  have := epi_is_cokernel_of_kernel _
    (pullback_to_biproduct_is_kernel.is_limit_pullback_to_biproduct f g),
  -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
  obtain ⟨d, hd⟩ := cokernel_cofork.is_colimit.desc' this u hu,
  change Z ⟶ R at d,
  change biprod.desc f (-g) ≫ d = u at hd,
  -- But then f ≫ d = 0:
  have : f ≫ d = 0, calc
    f ≫ d = (biprod.inl ≫ biprod.desc f (-g)) ≫ d : by rw biprod.inl_desc
    ... = biprod.inl ≫ u : by rw [category.assoc, hd]
    ... = 0 : biprod.inl_desc _ _,
  -- But f is an epimorphism, so d = 0...
  have : d = 0 := (cancel_epi f).1 (by simpa),
  -- ...or, in other words, e = 0.
  calc
    e = biprod.inr ≫ u : by rw biprod.inr_desc
    ... = biprod.inr ≫ biprod.desc f (-g) ≫ d : by rw ←hd
    ... = biprod.inr ≫ biprod.desc f (-g) ≫ 0 : by rw this
    ... = (biprod.inr ≫ biprod.desc f (-g)) ≫ 0 : by rw ←category.assoc
    ... = 0 : has_zero_morphisms.comp_zero _ _
end

/-- In an abelian category, the pullback of an epimorphism is an epimorphism. -/
instance epi_pullback_of_epi_g [epi g] : epi (pullback.fst : pullback f g ⟶ X) :=
-- It will suffice to consider some morphism e : X ⟶ R such that
-- pullback.fst ≫ e = 0 and show that e = 0.
epi_of_cancel_zero _ $ λ R e h,
begin
  -- Consider the morphism u := (e, 0) : X ⊞ Y ⟶ R.
  let u := biprod.desc e (0 : Y ⟶ R),
  -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
  have hu : pullback_to_biproduct_is_kernel.pullback_to_biproduct f g ≫ u = 0 := by simpa,
  -- pullback_to_biproduct f g is a kernel of (f, -g), so (f, -g) is a
  -- cokernel of pullback_to_biproduct f g
  have := epi_is_cokernel_of_kernel _
    (pullback_to_biproduct_is_kernel.is_limit_pullback_to_biproduct f g),
  -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
  obtain ⟨d, hd⟩ := cokernel_cofork.is_colimit.desc' this u hu,
  change Z ⟶ R at d,
  change biprod.desc f (-g) ≫ d = u at hd,
  -- But then (-g) ≫ d = 0:
  have : (-g) ≫ d = 0, calc
    (-g) ≫ d = (biprod.inr ≫ biprod.desc f (-g)) ≫ d : by rw biprod.inr_desc
    ... = biprod.inr ≫ u : by rw [category.assoc, hd]
    ... = 0 : biprod.inr_desc _ _,
  -- But g is an epimorphism, thus so is -g, so d = 0...
  have : d = 0 := (cancel_epi (-g)).1 (by simpa),
  -- ...or, in other words, e = 0.
  calc
    e = biprod.inl ≫ u : by rw biprod.inl_desc
    ... = biprod.inl ≫ biprod.desc f (-g) ≫ d : by rw ←hd
    ... = biprod.inl ≫ biprod.desc f (-g) ≫ 0 : by rw this
    ... = (biprod.inl ≫ biprod.desc f (-g)) ≫ 0 : by rw ←category.assoc
    ... = 0 : has_zero_morphisms.comp_zero _ _
end

lemma epi_snd_of_is_limit [epi f] {s : pullback_cone f g} (hs : is_limit s) : epi s.snd :=
begin
  convert epi_of_epi_fac (is_limit.cone_point_unique_up_to_iso_hom_comp (limit.is_limit _) hs _),
  { refl },
  { exact abelian.epi_pullback_of_epi_f _ _ }
end

lemma epi_fst_of_is_limit [epi g] {s : pullback_cone f g} (hs : is_limit s) : epi s.fst :=
begin
  convert epi_of_epi_fac (is_limit.cone_point_unique_up_to_iso_hom_comp (limit.is_limit _) hs _),
  { refl },
  { exact abelian.epi_pullback_of_epi_g _ _ }
end

/-- Suppose `f` and `g` are two morphisms with a common codomain and suppose we have written `g` as
    an epimorphism followed by a monomorphism. If `f` factors through the mono part of this
    factorization, then any pullback of `g` along `f` is an epimorphism. -/
lemma epi_fst_of_factor_thru_epi_mono_factorization
  (g₁ : Y ⟶ W) [epi g₁] (g₂ : W ⟶ Z) [mono g₂] (hg : g₁ ≫ g₂ = g) (f' : X ⟶ W) (hf : f' ≫ g₂ = f)
  (t : pullback_cone f g) (ht : is_limit t) : epi t.fst :=
by apply epi_fst_of_is_limit _ _ (pullback_cone.is_limit_of_factors f g g₂ f' g₁ hf hg t ht)

end epi_pullback

section mono_pushout
variables [limits.has_pushouts C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

instance mono_pushout_of_mono_f [mono f] : mono (pushout.inr : Z ⟶ pushout f g) :=
mono_of_cancel_zero _ $ λ R e h,
begin
  let u := biprod.lift (0 : R ⟶ Y) e,
  have hu : u ≫ biproduct_to_pushout_is_cokernel.biproduct_to_pushout f g = 0 := by simpa,
  have := mono_is_kernel_of_cokernel _
    (biproduct_to_pushout_is_cokernel.is_colimit_biproduct_to_pushout f g),
  obtain ⟨d, hd⟩ := kernel_fork.is_limit.lift' this u hu,
  change R ⟶ X at d,
  change d ≫ biprod.lift f (-g) = u at hd,
  have : d ≫ f = 0, calc
    d ≫ f = d ≫ biprod.lift f (-g) ≫ biprod.fst : by rw biprod.lift_fst
    ... = u ≫ biprod.fst : by rw [←category.assoc, hd]
    ... = 0 : biprod.lift_fst _ _,
  have : d = 0 := (cancel_mono f).1 (by simpa),
  calc
    e = u ≫ biprod.snd : by rw biprod.lift_snd
    ... = (d ≫ biprod.lift f (-g)) ≫ biprod.snd : by rw ←hd
    ... = (0 ≫ biprod.lift f (-g)) ≫ biprod.snd : by rw this
    ... = 0 ≫ biprod.lift f (-g) ≫ biprod.snd : by rw category.assoc
    ... = 0 : zero_comp
end

instance mono_pushout_of_mono_g [mono g] : mono (pushout.inl : Y ⟶ pushout f g) :=
mono_of_cancel_zero _ $ λ R e h,
begin
  let u := biprod.lift e (0 : R ⟶ Z),
  have hu : u ≫ biproduct_to_pushout_is_cokernel.biproduct_to_pushout f g = 0 := by simpa,
  have := mono_is_kernel_of_cokernel _
    (biproduct_to_pushout_is_cokernel.is_colimit_biproduct_to_pushout f g),
  obtain ⟨d, hd⟩ := kernel_fork.is_limit.lift' this u hu,
  change R ⟶ X at d,
  change d ≫ biprod.lift f (-g) = u at hd,
  have : d ≫ (-g) = 0, calc
    d ≫ (-g) = d ≫ biprod.lift f (-g) ≫ biprod.snd : by rw biprod.lift_snd
    ... = u ≫ biprod.snd : by rw [←category.assoc, hd]
    ... = 0 : biprod.lift_snd _ _,
  have : d = 0 := (cancel_mono (-g)).1 (by simpa),
  calc
    e = u ≫ biprod.fst : by rw biprod.lift_fst
    ... = (d ≫ biprod.lift f (-g)) ≫ biprod.fst : by rw ←hd
    ... = (0 ≫ biprod.lift f (-g)) ≫ biprod.fst : by rw this
    ... = 0 ≫ biprod.lift f (-g) ≫ biprod.fst : by rw category.assoc
    ... = 0 : zero_comp
end

lemma mono_inr_of_is_colimit [mono f] {s : pushout_cocone f g} (hs : is_colimit s) : mono s.inr :=
begin
  convert mono_of_mono_fac
    (is_colimit.comp_cocone_point_unique_up_to_iso_hom hs (colimit.is_colimit _) _),
  { refl },
  { exact abelian.mono_pushout_of_mono_f _ _ }
end

lemma mono_inl_of_is_colimit [mono g] {s : pushout_cocone f g} (hs : is_colimit s) : mono s.inl :=
begin
  convert mono_of_mono_fac
    (is_colimit.comp_cocone_point_unique_up_to_iso_hom hs (colimit.is_colimit _) _),
  { refl },
  { exact abelian.mono_pushout_of_mono_g _ _ }
end

/-- Suppose `f` and `g` are two morphisms with a common domain and suppose we have written `g` as
    an epimorphism followed by a monomorphism. If `f` factors through the epi part of this
    factorization, then any pushout of `g` along `f` is a monomorphism. -/
lemma mono_inl_of_factor_thru_epi_mono_factorization (f : X ⟶ Y) (g : X ⟶ Z)
  (g₁ : X ⟶ W) [epi g₁] (g₂ : W ⟶ Z) [mono g₂] (hg : g₁ ≫ g₂ = g) (f' : W ⟶ Y) (hf : g₁ ≫ f' = f)
  (t : pushout_cocone f g) (ht : is_colimit t) : mono t.inl :=
by apply mono_inl_of_is_colimit _ _ (pushout_cocone.is_colimit_of_factors _ _ _ _ _ hf hg t ht)

end mono_pushout

end category_theory.abelian

namespace category_theory.non_preadditive_abelian

variables (C : Type u) [category.{v} C] [non_preadditive_abelian C]

/-- Every non_preadditive_abelian category can be promoted to an abelian category. -/
def abelian : abelian C :=
{ has_finite_products := by apply_instance,
/- We need the `convert`s here because the instances we have are slightly different from the
   instances we need: `has_kernels` depends on an instance of `has_zero_morphisms`. In the
   case of `non_preadditive_abelian`, this instance is an explicit argument. However, in the case
   of `abelian`, the `has_zero_morphisms` instance is derived from `preadditive`. So we need to
   transform an instance of "has kernels with non_preadditive_abelian.has_zero_morphisms" to an
   instance of "has kernels with non_preadditive_abelian.preadditive.has_zero_morphisms". Luckily,
   we have a `subsingleton` instance for `has_zero_morphisms`, so `convert` can immediately close
   the goal it creates for the two instances of `has_zero_morphisms`, and the proof is complete. -/
  has_kernels := by convert (by apply_instance : limits.has_kernels C),
  has_cokernels := by convert (by apply_instance : limits.has_cokernels C),
  normal_mono_of_mono := by { introsI, convert normal_mono_of_mono f },
  normal_epi_of_epi := by { introsI, convert normal_epi_of_epi f },
  ..non_preadditive_abelian.preadditive }

end category_theory.non_preadditive_abelian

#lint
