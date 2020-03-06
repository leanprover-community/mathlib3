/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.limits.shapes.equalizers

/-!
# Categorical images

We define the categorical image of `f` as a factorisation `f = e ≫ m` through a monomorphism `m`,
so that `m` factors through the `m'` in any other such factorisation.

## Main statements

* When `C` has equalizers, the morphism `m` is an epimorphism.

## Future work
* TODO: coimages, and abelian categories.
* TODO: connect this with existing working in the group theory and ring theory libraries.

-/

universes v u

open category_theory
open category_theory.limits.walking_parallel_pair

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables {X Y : C} (f : X ⟶ Y)

/-- A factorisation of a morphism `f = e ≫ m`, with `m` monic. -/
-- FIXME I think there is a bug in the linter. Why should you expect an inhabited instance here?
@[nolint has_inhabited_instance]
structure mono_factorisation (f : X ⟶ Y) :=
(I : C)
(m : I ⟶ Y)
[m_mono : mono.{v} m]
(e : X ⟶ I)
(fac' : e ≫ m = f . obviously)

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely determined. -/
@[ext]
lemma mono_factorisation.ext
  {F F' : mono_factorisation f} (hI : F.I = F'.I) (hm : F.m = (eq_to_hom hI) ≫ F'.m) : F = F' :=
begin
  cases F, cases F',
  cases hI,
  simp at hm,
  dsimp at F_fac' F'_fac',
  congr,
  { assumption },
  { resetI, apply (cancel_mono F_m).1,
    rw [F_fac', hm, F'_fac'], }
end

/-- Data exhibiting that a morphism `f` has an image. -/
class has_image (f : X ⟶ Y) :=
(F : mono_factorisation f)
(lift : Π (F' : mono_factorisation f), F.I ⟶ F'.I)
(lift_fac' : Π (F' : mono_factorisation f), lift F' ≫ F'.m = F.m)

variable [has_image f]

/-- The categorical image of a morphism. -/
def image : C := (has_image.F f).I
/-- The inclusion of the image of a morphism into the target. -/
def image.ι : image f ⟶ Y := (has_image.F f).m
instance : mono (image.ι f) := (has_image.F f).m_mono

/-- The map from the source to the image of a morphism. -/
def factor_thru_image : X ⟶ image f := (has_image.F f).e
@[simp, reassoc]
lemma image.fac : factor_thru_image f ≫ image.ι f = f := (has_image.F f).fac'

variable {f}
/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the image. -/
def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I := has_image.lift F'
@[simp, reassoc]
lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
has_image.lift_fac' F'

-- TODO we could put a category structure on `mono_factorisation f`,
-- with the morphisms being `g : I ⟶ I'` commuting with the `m`s
-- (they then automatically commute with the `e`s)
-- and show that an `image_of f` gives an initial object there
-- (uniqueness of the lift comes for free).

instance lift_mono (F' : mono_factorisation f) : mono.{v} (image.lift F') :=
begin
  split, intros Z a b w,
  have w' : a ≫ image.ι f = b ≫ image.ι f :=
  calc a ≫ image.ι f = a ≫ (image.lift F' ≫ F'.m) : by simp
                 ... = (a ≫ image.lift F') ≫ F'.m : by rw [category.assoc]
                 ... = (b ≫ image.lift F') ≫ F'.m : by rw w
                 ... = b ≫ (image.lift F' ≫ F'.m) : by rw [←category.assoc]
                 ... = b ≫ image.ι f : by simp,
  exact (cancel_mono (image.ι f)).1 w',
end
lemma has_image.uniq
  (F' : mono_factorisation f) (l : image f ⟶ F'.I) (w : l ≫ F'.m = image.ι f) :
  l = image.lift F' :=
begin
  haveI := F'.m_mono,
  apply (cancel_mono F'.m).1,
  rw w,
  simp,
end

/-- `has_images` represents a choice of image for every morphism -/
class has_images :=
(has_image : Π {X Y : C} (f : X ⟶ Y), has_image.{v} f)

attribute [instance] has_images.has_image

-- This is the proof from https://en.wikipedia.org/wiki/Image_(category_theory), which is taken from:
-- Mitchell, Barry (1965), Theory of categories, MR 0202787, p.12, Proposition 10.1
instance [has_equalizers.{v} C] : epi (factor_thru_image f) :=
⟨λ Z g h w,
begin
  let q := equalizer.ι g h,
  let e' := equalizer.lift _ _ _ w, -- TODO make more of the arguments to equalizer.lift implicit?
  let F' : mono_factorisation f :=
  { I := equalizer g h,
    m := q ≫ image.ι f,
    e := e' },
  let v := image.lift F',
  have t₀ : v ≫ q ≫ image.ι f = image.ι f := image.lift_fac F',
  have t : v ≫ q = 𝟙 (image f) := (cancel_mono_id (image.ι f)).1 (by { convert t₀ using 1, rw category.assoc }),
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`, but this isn't necessary.
  calc g = 𝟙 (image f) ≫ g : by rw [category.id_comp]
     ... = v ≫ q ≫ g       : by rw [←t, category.assoc]
     ... = v ≫ q ≫ h       : by rw [equalizer.condition g h]
     ... = 𝟙 (image f) ≫ h : by rw [←category.assoc, t]
     ... = h                : by rw [category.id_comp]
end⟩

end category_theory.limits
