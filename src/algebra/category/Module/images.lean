/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Module.abelian
import category_theory.limits.shapes.images

/-!
# The category of R-modules has images.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `Module R` is an abelian category.
-/

open category_theory
open category_theory.limits

universes u v

namespace Module

variables {R : Type u} [comm_ring R]

variables {G H : Module.{v} R} (f : G ⟶ H)

local attribute [ext] subtype.ext_val

section -- implementation details of `has_image` for Module; use the API, not these
/-- The image of a morphism in `Module R` is just the bundling of `linear_map.range f` -/
def image : Module R := Module.of R (linear_map.range f)

/-- The inclusion of `image f` into the target -/
def image.ι : image f ⟶ H := f.range.subtype

instance : mono (image.ι f) := concrete_category.mono_of_injective (image.ι f) subtype.val_injective

/-- The corestriction map to the image -/
def factor_thru_image : G ⟶ image f := f.range_restrict

lemma image.fac : factor_thru_image f ≫ image.ι f = f :=
by { ext, refl, }

local attribute [simp] image.fac

variables {f}
/-- The universal property for the image factorisation -/
noncomputable def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I :=
{ to_fun :=
  (λ x, F'.e (classical.indefinite_description _ x.2).1 : image f → F'.I),
  map_add' :=
  begin
    intros x y,
    haveI := F'.m_mono,
    apply (mono_iff_injective F'.m).1, apply_instance,
    rw [linear_map.map_add],
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _,
    rw [F'.fac],
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    refl,
  end,
  map_smul' := λ c x,
  begin
    haveI := F'.m_mono,
    apply (mono_iff_injective F'.m).1, apply_instance,
    rw [linear_map.map_smul],
    change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _,
    rw [F'.fac],
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    refl,
  end }

lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
begin
  ext x,
  change (F'.e ≫ F'.m) _ = _,
  rw [F'.fac, (classical.indefinite_description _ x.2).2],
  refl,
end
end

/-- The factorisation of any morphism in `Module R` through a mono. -/
def mono_factorisation : mono_factorisation f :=
{ I := image f,
  m := image.ι f,
  e := factor_thru_image f }

/-- The factorisation of any morphism in `Module R` through a mono has the universal property of
the image. -/
noncomputable def is_image : is_image (mono_factorisation f) :=
{ lift := image.lift,
  lift_fac' := image.lift_fac }

/--
The categorical image of a morphism in `Module R`
agrees with the linear algebraic range.
-/
noncomputable def image_iso_range {G H : Module.{v} R} (f : G ⟶ H) :
  limits.image f ≅ Module.of R f.range :=
is_image.iso_ext (image.is_image f) (is_image f)

@[simp, reassoc, elementwise]
lemma image_iso_range_inv_image_ι {G H : Module.{v} R} (f : G ⟶ H) :
  (image_iso_range f).inv ≫ limits.image.ι f = Module.of_hom f.range.subtype :=
is_image.iso_ext_inv_m _ _

@[simp, reassoc, elementwise]
lemma image_iso_range_hom_subtype {G H : Module.{v} R} (f : G ⟶ H) :
  (image_iso_range f).hom ≫ Module.of_hom f.range.subtype = limits.image.ι f :=
by erw [←image_iso_range_inv_image_ι f, iso.hom_inv_id_assoc]

end Module
