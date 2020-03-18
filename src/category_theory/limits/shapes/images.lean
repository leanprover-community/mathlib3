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
structure mono_factorisation (f : X ⟶ Y) :=
(I : C)
(m : I ⟶ Y)
[m_mono : mono.{v} m]
(e : X ⟶ I)
(fac' : e ≫ m = f . obviously)

restate_axiom mono_factorisation.fac'
attribute [simp, reassoc] mono_factorisation.fac

namespace mono_factorisation

/-- The obvious factorisation of a monomorphism through itself. -/
def self [mono f] : mono_factorisation f :=
{ I := X,
  m := f,
  e := 𝟙 X }

-- I'm not sure we really need this, but the linter says that an inhabited instance ought to exist...
instance [mono f] : inhabited (mono_factorisation f) := ⟨self f⟩

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely determined. -/
@[ext]
lemma ext
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

end mono_factorisation

variable {f}

/-- Data exhibiting that a given factorisation through a mono is initial. -/
structure is_image (F : mono_factorisation f) :=
(lift : Π (F' : mono_factorisation f), F.I ⟶ F'.I)
(lift_fac' : Π (F' : mono_factorisation f), lift F' ≫ F'.m = F.m . obviously)

restate_axiom is_image.lift_fac'
attribute [simp, reassoc] is_image.lift_fac

variable (f)

namespace is_image

/-- The trivial factorisation of a monomorphism satisfies the universal property. -/
@[simps]
def self [mono f] : is_image (mono_factorisation.self f) :=
{ lift := λ F', F'.e }

instance [mono f] : inhabited (is_image (mono_factorisation.self f)) :=
⟨self f⟩

variable {f}
/-- Two factorisations through monomorphisms satisfying the universal property
must factor through isomorphic objects. -/
-- TODO this is another good candidate for a future `unique_up_to_canonical_iso`.
@[simps]
def iso_ext {F F' : mono_factorisation f} (hF : is_image F) (hF' : is_image F') : F.I ≅ F'.I :=
{ hom := hF.lift F',
  inv := hF'.lift F,
  hom_inv_id' := begin haveI := F.m_mono, apply (cancel_mono F.m).1, simp end,
  inv_hom_id' := begin haveI := F'.m_mono, apply (cancel_mono F'.m).1, simp end }

end is_image

/-- Data exhibiting that a morphism `f` has an image. -/
class has_image (f : X ⟶ Y) :=
(F : mono_factorisation f)
(is_image : is_image F)

section
variable [has_image f]

/-- The chosen factorisation of `f` through a monomorphism. -/
def image.mono_factorisation : mono_factorisation f := has_image.F f
/-- The witness of the universal property for the chosen factorisation of `f` through a monomorphism. -/
def image.is_image : is_image (image.mono_factorisation f) := has_image.is_image f

/-- The categorical image of a morphism. -/
def image : C := (image.mono_factorisation f).I
/-- The inclusion of the image of a morphism into the target. -/
def image.ι : image f ⟶ Y := (image.mono_factorisation f).m
@[simp] lemma image.as_ι : (image.mono_factorisation f).m = image.ι f := rfl
instance : mono (image.ι f) := (image.mono_factorisation f).m_mono
/-- The 'corestriction' morphism from the source to the image. -/
def image.c : X ⟶ image f := (image.mono_factorisation f).e
@[simp] lemma image.as_c : (image.mono_factorisation f).e = image.c f := rfl
@[simp] lemma image.c_ι : image.c f ≫ image.ι f = f := by erw (image.mono_factorisation f).fac

/-- The map from the source to the image of a morphism. -/
def factor_thru_image : X ⟶ image f := (image.mono_factorisation f).e
@[simp, reassoc]
lemma image.fac : factor_thru_image f ≫ image.ι f = f := (image.mono_factorisation f).fac'

variable {f}
/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the image. -/
def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I := (image.is_image f).lift F'
@[simp, reassoc]
lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
(image.is_image f).lift_fac' F'

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
end

/-- `has_images` represents a choice of image for every morphism -/
class has_images :=
(has_image : Π {X Y : C} (f : X ⟶ Y), has_image.{v} f)

attribute [instance, priority 100] has_images.has_image

section
variables (f) [has_image f]
/-- The image of a monomorphism is isomorphic to the source. -/
def image_mono_iso_source [mono f] : image f ≅ X :=
is_image.iso_ext (image.is_image f) (is_image.self f)

@[simp, reassoc]
lemma image_mono_iso_source_inv_ι [mono f] : (image_mono_iso_source f).inv ≫ image.ι f = f :=
by simp [image_mono_iso_source]
@[simp, reassoc]
lemma image_mono_iso_source_hom_self [mono f] : (image_mono_iso_source f).hom ≫ f = image.ι f :=
begin
  conv { to_lhs, congr, skip, rw ←image_mono_iso_source_inv_ι f, },
  rw [←category.assoc, iso.hom_inv_id, category.id_comp],
end

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
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`,
  -- and concludes that `equalizer g h ≅ image f`,
  -- but this isn't necessary.
  calc g = 𝟙 (image f) ≫ g : by rw [category.id_comp]
     ... = v ≫ q ≫ g       : by rw [←t, category.assoc]
     ... = v ≫ q ≫ h       : by rw [equalizer.condition g h]
     ... = 𝟙 (image f) ≫ h : by rw [←category.assoc, t]
     ... = h                : by rw [category.id_comp]
end⟩
end

section
variables {f} {f' : X ⟶ Y} [has_image f] [has_image f']

/-- An equation between morphisms gives a comparison map between the images (which momentarily we prove is an iso). -/
def image.eq_to_hom (h : f = f') : image f ⟶ image f' :=
image.lift.{v}
{ I := image f',
  m := image.ι f',
  e := factor_thru_image f', }.

instance (h : f = f') : is_iso (image.eq_to_hom h) :=
{ inv := image.eq_to_hom h.symm,
  hom_inv_id' := begin apply (cancel_mono (image.ι f)).1, dsimp [image.eq_to_hom], simp, end,
  inv_hom_id' := begin apply (cancel_mono (image.ι f')).1, dsimp [image.eq_to_hom], simp, end, }

/-- An equation between morphisms gives an isomorphism between the images. -/
def image.eq_to_iso (h : f = f') : image f ≅ image f' := as_iso (image.eq_to_hom h)
end

section
variables {Z : C} (g : Y ⟶ Z)

/-- The comparison map `image (f ≫ g) ⟶ image g`. -/
def image.pre_comp [has_image g] [has_image (f ≫ g)] : image (f ≫ g) ⟶ image g :=
image.lift.{v}
{ I := image g,
  m := image.ι g,
  e := f ≫ factor_thru_image g }

/--
The two step comparison map
  `image (f ≫ (g ≫ h)) ⟶ image (g ≫ h) ⟶ image h`
agrees with the one step comparison map
  `image (f ≫ (g ≫ h)) ≅ image ((f ≫ g) ≫ h) ⟶ image h`.
 -/
lemma image.pre_comp_comp {W : C} (h : Z ⟶ W)
  [has_image (g ≫ h)] [has_image (f ≫ g ≫ h)]
  [has_image h] [has_image ((f ≫ g) ≫ h)] :
image.pre_comp f (g ≫ h) ≫ image.pre_comp g h = image.eq_to_hom (category.assoc C f g h).symm ≫ (image.pre_comp (f ≫ g) h) :=
begin
  apply (cancel_mono (image.ι h)).1,
  dsimp [image.pre_comp, image.eq_to_hom],
  simp,
end

-- Note that in general we don't have the other comparison map you might expect
-- `image f ⟶ image (f ≫ g)`.

end

end category_theory.limits
