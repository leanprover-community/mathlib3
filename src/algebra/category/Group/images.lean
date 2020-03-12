/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group
import category_theory.limits.shapes.images
import group_theory.subgroup
import algebra.group_power

/-!
# The category of commutative additive groups has images.
-/

open category_theory
open category_theory.limits

universe u

namespace AddCommGroup

variables {G H : AddCommGroup.{0}} (f : G ⟶ H)

local attribute [ext] subtype.eq'

section -- implementation details of `has_image` for AddCommGroup; use the API, not these
/-- the image of a morphism in AddCommGroup is just the bundling of `set.range f` -/
def image : AddCommGroup := AddCommGroup.of (set.range f)
/-- the inclusion of `image f` into the target -/
-- TODO it would be nicer to reuse existing unbundled machinery here: does it exist?
def image.ι : image f ⟶ H := (⟨subtype.val, rfl, by { intros, refl }⟩ : image f →+ H)
instance : mono (image.ι f) :=
begin
  split, intros, ext,
  convert congr_arg (λ k : Z ⟶ H, (k : _ →+ _) x) w,
end
/-- the corestriction map to the image -/
-- TODO it would be nicer to reuse existing unbundled machinery here: does it exist?
def factor_thru_image : G ⟶ image f :=
{ to_fun := λ g, ⟨f g, ⟨g, rfl⟩⟩,
  map_zero' := by { ext, dsimp, erw add_monoid_hom.map_zero f, refl, },
  map_add' := by { intros, ext, dsimp, erw add_monoid_hom.map_add f, refl, } }
lemma image.fac : factor_thru_image f ≫ image.ι f = f :=
by { ext, refl, }

local attribute [simp] image.fac

variables {f}
/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I :=
{ to_fun :=
  (λ x, F'.e (classical.indefinite_description _ x.2).1 : image f → F'.I),
  map_zero' :=
  begin
    haveI := F'.m_mono,
    apply injective_of_mono F'.m,
    change (F'.e ≫ F'.m) _ = _,
    rw [F'.fac, add_monoid_hom.map_zero],
    convert (classical.indefinite_description (λ y, f y = 0) _).2,
  end,
  map_add' :=
  begin
    intros x y,
    haveI := F'.m_mono,
    apply injective_of_mono F'.m,
    rw [add_monoid_hom.map_add],
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _,
    rw [F'.fac],
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    rw (classical.indefinite_description (λ z, f z = _) _).2,
    refl,
  end,
 }
lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
begin
  ext x,
  change (F'.e ≫ F'.m) _ = _,
  rw [F'.fac, (classical.indefinite_description _ x.2).2],
  refl,
end
end

/-- the factorisation of any morphism in AddCommGroup through a mono. -/
def mono_factorisation : mono_factorisation f :=
{ I := image f,
  m := image.ι f,
  e := factor_thru_image f }

noncomputable instance : has_image f :=
{ F := mono_factorisation f,
  lift := image.lift,
  lift_fac' := image.lift_fac }

noncomputable instance : has_images.{0} AddCommGroup.{0} :=
{ has_image := infer_instance }

end AddCommGroup
