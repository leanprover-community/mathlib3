/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.strong_epi

/-!
# Categorical images

We define the categorical image of `f` as a factorisation `f = e ≫ m` through a monomorphism `m`,
so that `m` factors through the `m'` in any other such factorisation.

## Main definitions

* A `mono_factorisation` is a factorisation `f = e ≫ m`, where `m` is a monomorphism
* `is_image F` means that a given mono factorisation `F` has the universal property of the image.
* `has_image f` means that we have chosen an image for the morphism `f : X ⟶ Y`.
  * In this case, `image f` is the image object, `image.ι f : image f ⟶ Y` is the monomorphism `m`
    of the factorisation and `factor_thru_image f : X ⟶ image f` is the morphism `e`.
* `has_images C` means that every morphism in `C` has an image.
* Let `f : X ⟶ Y` and `g : P ⟶ Q` be morphisms in `C`, which we will represent as objects of the
  arrow category `arrow C`. Then `sq : f ⟶ g` is a commutative square in `C`. If `f` and `g` have
  images, then `has_image_map sq` represents the fact that there is a morphism
  `i : image f ⟶ image g` making the diagram

  X ----→ image f ----→ Y
  |         |           |
  |         |           |
  ↓         ↓           ↓
  P ----→ image g ----→ Q

  commute, where the top row is the image factorisation of `f`, the bottom row is the image
  factorisation of `g`, and the outer rectangle is the commutative square `sq`.
* If a category `has_images`, then `has_image_maps` means that every commutative square admits an
  image map.
* If a category `has_images`, then `has_strong_epi_images` means that the morphism to the image is
  always a strong epimorphism.

## Main statements

* When `C` has equalizers, the morphism `e` appearing in an image factorisation is an epimorphism.
* When `C` has strong epi images, then these images admit image maps.

## Future work
* TODO: coimages, and abelian categories.
* TODO: connect this with existing working in the group theory and ring theory libraries.

-/

noncomputable theory

universes v u

open category_theory
open category_theory.limits.walking_parallel_pair

namespace category_theory.limits

variables {C : Type u} [category.{v} C]

variables {X Y : C} (f : X ⟶ Y)

/-- A factorisation of a morphism `f = e ≫ m`, with `m` monic. -/
structure mono_factorisation (f : X ⟶ Y) :=
(I : C)
(m : I ⟶ Y)
[m_mono : mono m]
(e : X ⟶ I)
(fac' : e ≫ m = f . obviously)

restate_axiom mono_factorisation.fac'
attribute [simp, reassoc] mono_factorisation.fac
attribute [instance] mono_factorisation.m_mono

attribute [instance] mono_factorisation.m_mono

namespace mono_factorisation

/-- The obvious factorisation of a monomorphism through itself. -/
def self [mono f] : mono_factorisation f :=
{ I := X,
  m := f,
  e := 𝟙 X }

-- I'm not sure we really need this, but the linter says that an inhabited instance
-- ought to exist...
instance [mono f] : inhabited (mono_factorisation f) := ⟨self f⟩

variables {f}

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely
determined. -/
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

/-- Any mono factorisation of `f` gives a mono factorisation of `f ≫ g` when `g` is a mono. -/
@[simps]
def comp_mono (F : mono_factorisation f) {Y' : C} (g : Y ⟶ Y') [mono g] :
  mono_factorisation (f ≫ g) :=
{ I := F.I,
  m := F.m ≫ g,
  m_mono := mono_comp _ _,
  e := F.e, }

/-- A mono factorisation of `f ≫ g`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
def of_comp_iso {Y' : C} {g : Y ⟶ Y'} [is_iso g] (F : mono_factorisation (f ≫ g)) :
  mono_factorisation f :=
{ I := F.I,
  m := F.m ≫ (inv g),
  m_mono := mono_comp _ _,
  e := F.e, }

/-- Any mono factorisation of `f` gives a mono factorisation of `g ≫ f`. -/
@[simps]
def iso_comp (F : mono_factorisation f) {X' : C} (g : X' ⟶ X) :
  mono_factorisation (g ≫ f) :=
{ I := F.I,
  m := F.m,
  e := g ≫ F.e, }

/-- A mono factorisation of `g ≫ f`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
def of_iso_comp {X' : C} (g : X' ⟶ X) [is_iso g] (F : mono_factorisation (g ≫ f)) :
  mono_factorisation f :=
{ I := F.I,
  m := F.m,
  e := inv g ≫ F.e, }

end mono_factorisation

variable {f}

/-- Data exhibiting that a given factorisation through a mono is initial. -/
structure is_image (F : mono_factorisation f) :=
(lift : Π (F' : mono_factorisation f), F.I ⟶ F'.I)
(lift_fac' : Π (F' : mono_factorisation f), lift F' ≫ F'.m = F.m . obviously)

restate_axiom is_image.lift_fac'
attribute [simp, reassoc] is_image.lift_fac

@[simp, reassoc] lemma is_image.fac_lift {F : mono_factorisation f} (hF : is_image F)
  (F' : mono_factorisation f) : F.e ≫ hF.lift F' = F'.e :=
(cancel_mono F'.m).1 $ by simp

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
  hom_inv_id' := (cancel_mono F.m).1 (by simp),
  inv_hom_id' := (cancel_mono F'.m).1 (by simp) }

variables {F F' : mono_factorisation f} (hF : is_image F) (hF' : is_image F')

lemma iso_ext_hom_m : (iso_ext hF hF').hom ≫ F'.m = F.m := by simp
lemma iso_ext_inv_m : (iso_ext hF hF').inv ≫ F.m = F'.m := by simp
lemma e_iso_ext_hom : F.e ≫ (iso_ext hF hF').hom = F'.e := by simp
lemma e_iso_ext_inv : F'.e ≫ (iso_ext hF hF').inv = F.e := by simp

end is_image

/-- Data exhibiting that a morphism `f` has an image. -/
structure image_factorisation (f : X ⟶ Y) :=
(F : mono_factorisation f)
(is_image : is_image F)

instance inhabited_image_factorisation (f : X ⟶ Y) [mono f] : inhabited (image_factorisation f) :=
⟨⟨_, is_image.self f⟩⟩

/-- `has_image f` means that there exists an image factorisation of `f`. -/
class has_image (f : X ⟶ Y) : Prop :=
mk' :: (exists_image : nonempty (image_factorisation f))

lemma has_image.mk {f : X ⟶ Y} (F : image_factorisation f) : has_image f :=
⟨nonempty.intro F⟩

section
variable [has_image f]

/-- The chosen factorisation of `f` through a monomorphism. -/
def image.mono_factorisation : mono_factorisation f :=
(classical.choice (has_image.exists_image)).F

/-- The witness of the universal property for the chosen factorisation of `f` through
a monomorphism. -/
def image.is_image : is_image (image.mono_factorisation f) :=
(classical.choice (has_image.exists_image)).is_image

/-- The categorical image of a morphism. -/
def image : C := (image.mono_factorisation f).I
/-- The inclusion of the image of a morphism into the target. -/
def image.ι : image f ⟶ Y := (image.mono_factorisation f).m
@[simp] lemma image.as_ι : (image.mono_factorisation f).m = image.ι f := rfl
instance : mono (image.ι f) := (image.mono_factorisation f).m_mono

/-- The map from the source to the image of a morphism. -/
def factor_thru_image : X ⟶ image f := (image.mono_factorisation f).e
/-- Rewrite in terms of the `factor_thru_image` interface. -/
@[simp]
lemma as_factor_thru_image : (image.mono_factorisation f).e = factor_thru_image f := rfl
@[simp, reassoc]
lemma image.fac : factor_thru_image f ≫ image.ι f = f := (image.mono_factorisation f).fac'

variable {f}

/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the
image. -/
def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I := (image.is_image f).lift F'
@[simp, reassoc]
lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
(image.is_image f).lift_fac' F'
@[simp, reassoc]
lemma image.fac_lift (F' : mono_factorisation f) : factor_thru_image f ≫ image.lift F' = F'.e :=
(image.is_image f).fac_lift F'

@[simp, reassoc]
lemma is_image.lift_ι {F : mono_factorisation f} (hF : is_image F) :
  hF.lift (image.mono_factorisation f) ≫ image.ι f = F.m :=
hF.lift_fac _

-- TODO we could put a category structure on `mono_factorisation f`,
-- with the morphisms being `g : I ⟶ I'` commuting with the `m`s
-- (they then automatically commute with the `e`s)
-- and show that an `image_of f` gives an initial object there
-- (uniqueness of the lift comes for free).

instance lift_mono (F' : mono_factorisation f) : mono (image.lift F') :=
by { apply mono_of_mono _ F'.m, simpa using mono_factorisation.m_mono _ }

lemma has_image.uniq
  (F' : mono_factorisation f) (l : image f ⟶ F'.I) (w : l ≫ F'.m = image.ι f) :
  l = image.lift F' :=
(cancel_mono F'.m).1 (by simp [w])

/-- If `has_image g`, then `has_image (f ≫ g)` when `f` is an isomorphism. -/
instance {X Y Z : C} (f : X ⟶ Y) [is_iso f] (g : Y ⟶ Z) [has_image g] : has_image (f ≫ g) :=
{ exists_image := ⟨{
  F :=
  { I := image g,
    m := image.ι g,
    e := f ≫ factor_thru_image g, },
  is_image := { lift := λ F', image.lift { I := F'.I, m := F'.m, e := inv f ≫ F'.e, }, }, }⟩ }

end

section
variables (C)

/-- `has_images` represents a choice of image for every morphism -/
class has_images :=
(has_image : Π {X Y : C} (f : X ⟶ Y), has_image f)

attribute [instance, priority 100] has_images.has_image
end

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

-- This is the proof that `factor_thru_image f` is an epimorphism
-- from https://en.wikipedia.org/wiki/Image_%28category_theory%29, which is in turn taken from:
-- Mitchell, Barry (1965), Theory of categories, MR 0202787, p.12, Proposition 10.1
@[ext]
lemma image.ext {W : C} {g h : image f ⟶ W} [has_limit (parallel_pair g h)]
  (w : factor_thru_image f ≫ g = factor_thru_image f ≫ h) :
  g = h :=
begin
  let q := equalizer.ι g h,
  let e' := equalizer.lift _ w,
  let F' : mono_factorisation f :=
  { I := equalizer g h,
    m := q ≫ image.ι f,
    m_mono := by apply mono_comp,
    e := e' },
  let v := image.lift F',
  have t₀ : v ≫ q ≫ image.ι f = image.ι f := image.lift_fac F',
  have t : v ≫ q = 𝟙 (image f) :=
    (cancel_mono_id (image.ι f)).1 (by { convert t₀ using 1, rw category.assoc }),
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`,
  -- and concludes that `equalizer g h ≅ image f`,
  -- but this isn't necessary.
  calc g = 𝟙 (image f) ≫ g : by rw [category.id_comp]
     ... = v ≫ q ≫ g       : by rw [←t, category.assoc]
     ... = v ≫ q ≫ h       : by rw [equalizer.condition g h]
     ... = 𝟙 (image f) ≫ h : by rw [←category.assoc, t]
     ... = h                : by rw [category.id_comp]
end

instance [Π {Z : C} (g h : image f ⟶ Z), has_limit (parallel_pair g h)] :
  epi (factor_thru_image f) :=
⟨λ Z g h w, image.ext f w⟩

lemma epi_image_of_epi {X Y : C} (f : X ⟶ Y) [has_image f] [E : epi f] : epi (image.ι f) :=
begin
  rw ←image.fac f at E,
  resetI,
  exact epi_of_epi (factor_thru_image f) (image.ι f),
end

lemma epi_of_epi_image {X Y : C} (f : X ⟶ Y) [has_image f]
  [epi (image.ι f)] [epi (factor_thru_image f)] : epi f :=
by { rw [←image.fac f], apply epi_comp, }

end

section
variables {f} {f' : X ⟶ Y} [has_image f] [has_image f']

/--
An equation between morphisms gives a comparison map between the images
(which momentarily we prove is an iso).
-/
def image.eq_to_hom (h : f = f') : image f ⟶ image f' :=
image.lift
{ I := image f',
  m := image.ι f',
  e := factor_thru_image f', }.

instance (h : f = f') : is_iso (image.eq_to_hom h) :=
⟨⟨image.eq_to_hom h.symm,
  ⟨(cancel_mono (image.ι f)).1 (by simp [image.eq_to_hom]),
   (cancel_mono (image.ι f')).1 (by simp [image.eq_to_hom])⟩⟩⟩

/-- An equation between morphisms gives an isomorphism between the images. -/
def image.eq_to_iso (h : f = f') : image f ≅ image f' := as_iso (image.eq_to_hom h)

/--
As long as the category has equalizers,
the image inclusion maps commute with `image.eq_to_iso`.
-/
lemma image.eq_fac [has_equalizers C] (h : f = f') :
  image.ι f = (image.eq_to_iso h).hom ≫ image.ι f' :=
by { ext, simp [image.eq_to_iso, image.eq_to_hom], }

end

section
variables {Z : C} (g : Y ⟶ Z)

/-- The comparison map `image (f ≫ g) ⟶ image g`. -/
def image.pre_comp [has_image g] [has_image (f ≫ g)] : image (f ≫ g) ⟶ image g :=
image.lift
{ I := image g,
  m := image.ι g,
  e := f ≫ factor_thru_image g }

@[simp, reassoc]
lemma image.pre_comp_ι [has_image g] [has_image (f ≫ g)] :
  image.pre_comp f g ≫ image.ι g = image.ι (f ≫ g) :=
by simp [image.pre_comp]

@[simp, reassoc]
lemma image.factor_thru_image_pre_comp [has_image g] [has_image (f ≫ g)] :
  factor_thru_image (f ≫ g) ≫ image.pre_comp f g = f ≫ factor_thru_image g :=
by simp [image.pre_comp]

/--
`image.pre_comp f g` is a monomorphism.
-/
instance image.pre_comp_mono [has_image g] [has_image (f ≫ g)] : mono (image.pre_comp f g) :=
begin
  apply mono_of_mono _ (image.ι g),
  simp only [image.pre_comp_ι],
  apply_instance,
end

/--
The two step comparison map
  `image (f ≫ (g ≫ h)) ⟶ image (g ≫ h) ⟶ image h`
agrees with the one step comparison map
  `image (f ≫ (g ≫ h)) ≅ image ((f ≫ g) ≫ h) ⟶ image h`.
 -/
lemma image.pre_comp_comp {W : C} (h : Z ⟶ W)
  [has_image (g ≫ h)] [has_image (f ≫ g ≫ h)]
  [has_image h] [has_image ((f ≫ g) ≫ h)] :
  image.pre_comp f (g ≫ h) ≫ image.pre_comp g h =
    image.eq_to_hom (category.assoc f g h).symm ≫ (image.pre_comp (f ≫ g) h) :=
begin
  apply (cancel_mono (image.ι h)).1,
  simp [image.pre_comp, image.eq_to_hom],
end

variables [has_equalizers C]

/--
`image.pre_comp f g` is an epimorphism when `f` is an epimorphism
(we need `C` to have equalizers to prove this).
-/
instance image.pre_comp_epi_of_epi [has_image g] [has_image (f ≫ g)] [epi f] :
  epi (image.pre_comp f g) :=
begin
  apply epi_of_epi_fac (image.factor_thru_image_pre_comp _ _),
  exact epi_comp _ _
end

instance has_image_iso_comp [is_iso f] [has_image g] : has_image (f ≫ g) :=
has_image.mk
{ F := (image.mono_factorisation g).iso_comp f,
  is_image := { lift := λ F', image.lift (F'.of_iso_comp f) }, }

/--
`image.pre_comp f g` is an isomorphism when `f` is an isomorphism
(we need `C` to have equalizers to prove this).
-/
instance image.is_iso_precomp_iso (f : X ⟶ Y) [is_iso f] [has_image g] :
  is_iso (image.pre_comp f g) :=
⟨⟨image.lift
  { I := image (f ≫ g),
    m := image.ι (f ≫ g),
    e := inv f ≫ factor_thru_image (f ≫ g) },
  ⟨by { ext, simp [image.pre_comp], }, by { ext, simp [image.pre_comp], }⟩⟩⟩

-- Note that in general we don't have the other comparison map you might expect
-- `image f ⟶ image (f ≫ g)`.

instance has_image_comp_iso [has_image f] [is_iso g] : has_image (f ≫ g) :=
has_image.mk
{ F := (image.mono_factorisation f).comp_mono g,
  is_image := { lift := λ F', image.lift F'.of_comp_iso }, }

/-- Postcomposing by an isomorphism induces an isomorphism on the image. -/
def image.comp_iso [has_image f] [is_iso g] :
  image f ≅ image (f ≫ g) :=
{ hom := image.lift (image.mono_factorisation (f ≫ g)).of_comp_iso,
  inv := image.lift ((image.mono_factorisation f).comp_mono g) }

@[simp, reassoc] lemma image.comp_iso_hom_comp_image_ι [has_image f] [is_iso g] :
  (image.comp_iso f g).hom ≫ image.ι (f ≫ g) = image.ι f ≫ g :=
by { ext, simp [image.comp_iso] }

@[simp, reassoc] lemma image.comp_iso_inv_comp_image_ι [has_image f] [is_iso g] :
  (image.comp_iso f g).inv ≫ image.ι f = image.ι (f ≫ g) ≫ inv g :=
by { ext, simp [image.comp_iso] }

end

end category_theory.limits

namespace category_theory.limits

variables {C : Type u} [category.{v} C]

section

instance {X Y : C} (f : X ⟶ Y) [has_image f] : has_image (arrow.mk f).hom :=
show has_image f, by apply_instance

end

section has_image_map

/-- An image map is a morphism `image f → image g` fitting into a commutative square and satisfying
    the obvious commutativity conditions. -/
structure image_map {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g) :=
(map : image f.hom ⟶ image g.hom)
(map_ι' : map ≫ image.ι g.hom = image.ι f.hom ≫ sq.right . obviously)

instance inhabited_image_map {f : arrow C} [has_image f.hom] : inhabited (image_map (𝟙 f)) :=
⟨⟨𝟙 _, by tidy⟩⟩

restate_axiom image_map.map_ι'
attribute [simp, reassoc] image_map.map_ι

@[simp, reassoc]
lemma image_map.factor_map {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g)
  (m : image_map sq) :
  factor_thru_image f.hom ≫ m.map = sq.left ≫ factor_thru_image g.hom :=
(cancel_mono (image.ι g.hom)).1 $ by simp

/-- To give an image map for a commutative square with `f` at the top and `g` at the bottom, it
    suffices to give a map between any mono factorisation of `f` and any image factorisation of
    `g`. -/
def image_map.transport {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g)
  (F : mono_factorisation f.hom) {F' : mono_factorisation g.hom} (hF' : is_image F')
  {map : F.I ⟶ F'.I} (map_ι : map ≫ F'.m = F.m ≫ sq.right) : image_map sq :=
{ map := image.lift F ≫ map ≫ hF'.lift (image.mono_factorisation g.hom),
  map_ι' := by simp [map_ι] }

/-- `has_image_map sq` means that there is an `image_map` for the square `sq`. -/
class has_image_map {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g) : Prop :=
mk' :: (has_image_map : nonempty (image_map sq))

lemma has_image_map.mk {f g : arrow C} [has_image f.hom] [has_image g.hom] {sq : f ⟶ g}
  (m : image_map sq) : has_image_map sq :=
⟨nonempty.intro m⟩

lemma has_image_map.transport {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g)
  (F : mono_factorisation f.hom) {F' : mono_factorisation g.hom} (hF' : is_image F')
  (map : F.I ⟶ F'.I) (map_ι : map ≫ F'.m = F.m ≫ sq.right) : has_image_map sq :=
has_image_map.mk $ image_map.transport sq F hF' map_ι

/-- Obtain an `image_map` from a `has_image_map` instance. -/
def has_image_map.image_map {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g)
  [has_image_map sq] : image_map sq :=
classical.choice $ @has_image_map.has_image_map _ _ _ _ _ _ sq _

variables {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g)

section
local attribute [ext] image_map

instance : subsingleton (image_map sq) :=
subsingleton.intro $ λ a b, image_map.ext a b $ (cancel_mono (image.ι g.hom)).1 $
  by simp only [image_map.map_ι]

end

variable [has_image_map sq]

/-- The map on images induced by a commutative square. -/
abbreviation image.map : image f.hom ⟶ image g.hom :=
(has_image_map.image_map sq).map

lemma image.factor_map :
  factor_thru_image f.hom ≫ image.map sq = sq.left ≫ factor_thru_image g.hom :=
by simp
lemma image.map_ι : image.map sq ≫ image.ι g.hom = image.ι f.hom ≫ sq.right :=
by simp
lemma image.map_hom_mk'_ι {X Y P Q : C} {k : X ⟶ Y} [has_image k] {l : P ⟶ Q} [has_image l]
  {m : X ⟶ P} {n : Y ⟶ Q} (w : m ≫ l = k ≫ n) [has_image_map (arrow.hom_mk' w)] :
  image.map (arrow.hom_mk' w) ≫ image.ι l = image.ι k ≫ n :=
image.map_ι _

section
variables {h : arrow C} [has_image h.hom] (sq' : g ⟶ h)
variables [has_image_map sq']

/-- Image maps for composable commutative squares induce an image map in the composite square. -/
def image_map_comp : image_map (sq ≫ sq') :=
{ map := image.map sq ≫ image.map sq' }

@[simp]
lemma image.map_comp [has_image_map (sq ≫ sq')] :
  image.map (sq ≫ sq') = image.map sq ≫ image.map sq' :=
show (has_image_map.image_map (sq ≫ sq')).map = (image_map_comp sq sq').map, by congr

end

section
variables (f)

/-- The identity `image f ⟶ image f` fits into the commutative square represented by the identity
    morphism `𝟙 f` in the arrow category. -/
def image_map_id : image_map (𝟙 f) :=
{ map := 𝟙 (image f.hom) }

@[simp]
lemma image.map_id [has_image_map (𝟙 f)] : image.map (𝟙 f) = 𝟙 (image f.hom) :=
show (has_image_map.image_map (𝟙 f)).map = (image_map_id f).map, by congr

end

end has_image_map

section
variables (C) [has_images C]

/-- If a category `has_image_maps`, then all commutative squares induce morphisms on images. -/
class has_image_maps :=
(has_image_map : Π {f g : arrow C} (st : f ⟶ g), has_image_map st)

attribute [instance, priority 100] has_image_maps.has_image_map

end

section has_image_maps
variables [has_images C] [has_image_maps C]

/-- The functor from the arrow category of `C` to `C` itself that maps a morphism to its image
    and a commutative square to the induced morphism on images. -/
@[simps]
def im : arrow C ⥤ C :=
{ obj := λ f, image f.hom,
  map := λ _ _ st, image.map st }

end has_image_maps

section strong_epi_mono_factorisation

/-- A strong epi-mono factorisation is a decomposition `f = e ≫ m` with `e` a strong epimorphism
    and `m` a monomorphism. -/
structure strong_epi_mono_factorisation {X Y : C} (f : X ⟶ Y) extends mono_factorisation f :=
[e_strong_epi : strong_epi e]

attribute [instance] strong_epi_mono_factorisation.e_strong_epi

/-- Satisfying the inhabited linter -/
instance strong_epi_mono_factorisation_inhabited {X Y : C} (f : X ⟶ Y) [strong_epi f] :
  inhabited (strong_epi_mono_factorisation f) :=
⟨⟨⟨Y, 𝟙 Y, f, by simp⟩⟩⟩

/-- A mono factorisation coming from a strong epi-mono factorisation always has the universal
    property of the image. -/
def strong_epi_mono_factorisation.to_mono_is_image {X Y : C} {f : X ⟶ Y}
  (F : strong_epi_mono_factorisation f) : is_image F.to_mono_factorisation :=
{ lift := λ G, arrow.lift $ arrow.hom_mk' $
    show G.e ≫ G.m = F.e ≫ F.m, by rw [F.to_mono_factorisation.fac, G.fac] }

variable (C)

/-- A category has strong epi-mono factorisations if every morphism admits a strong epi-mono
    factorisation. -/
class has_strong_epi_mono_factorisations : Prop :=
mk' :: (has_fac : Π {X Y : C} (f : X ⟶ Y), nonempty (strong_epi_mono_factorisation f))

variable {C}

lemma has_strong_epi_mono_factorisations.mk
  (d : Π {X Y : C} (f : X ⟶ Y), strong_epi_mono_factorisation f) :
  has_strong_epi_mono_factorisations C :=
⟨λ X Y f, nonempty.intro $ d f⟩

@[priority 100]
instance has_images_of_has_strong_epi_mono_factorisations
  [has_strong_epi_mono_factorisations C] : has_images C :=
{ has_image := λ X Y f,
  let F' := classical.choice (has_strong_epi_mono_factorisations.has_fac f) in
  has_image.mk { F := F'.to_mono_factorisation,
                 is_image := F'.to_mono_is_image } }

end strong_epi_mono_factorisation

section has_strong_epi_images
variables (C) [has_images C]

/-- A category has strong epi images if it has all images and `factor_thru_image f` is a strong
    epimorphism for all `f`. -/
class has_strong_epi_images : Prop :=
(strong_factor_thru_image : Π {X Y : C} (f : X ⟶ Y), strong_epi (factor_thru_image f))

attribute [instance] has_strong_epi_images.strong_factor_thru_image
end has_strong_epi_images

section has_strong_epi_images

/-- If there is a single strong epi-mono factorisation of `f`, then every image factorisation is a
    strong epi-mono factorisation. -/
lemma strong_epi_of_strong_epi_mono_factorisation {X Y : C} {f : X ⟶ Y}
  (F : strong_epi_mono_factorisation f) {F' : mono_factorisation f} (hF' : is_image F') :
  strong_epi F'.e :=
by { rw ←is_image.e_iso_ext_hom F.to_mono_is_image hF', apply strong_epi_comp }

lemma strong_epi_factor_thru_image_of_strong_epi_mono_factorisation {X Y : C} {f : X ⟶ Y}
  [has_image f] (F : strong_epi_mono_factorisation f) : strong_epi (factor_thru_image f) :=
strong_epi_of_strong_epi_mono_factorisation F $ image.is_image f

/-- If we constructed our images from strong epi-mono factorisations, then these images are
    strong epi images. -/
@[priority 100]
instance has_strong_epi_images_of_has_strong_epi_mono_factorisations
  [has_strong_epi_mono_factorisations C] : has_strong_epi_images C :=
{ strong_factor_thru_image := λ X Y f,
    strong_epi_factor_thru_image_of_strong_epi_mono_factorisation $
      classical.choice $ has_strong_epi_mono_factorisations.has_fac f }

end has_strong_epi_images

section has_strong_epi_images
variables [has_images C]

/-- A category with strong epi images has image maps. -/
@[priority 100]
instance has_image_maps_of_has_strong_epi_images [has_strong_epi_images C] :
  has_image_maps C :=
{ has_image_map := λ f g st, has_image_map.mk
  { map := arrow.lift $ arrow.hom_mk' $ show (st.left ≫ factor_thru_image g.hom) ≫ image.ι g.hom =
      factor_thru_image f.hom ≫ (image.ι f.hom ≫ st.right), by simp } }

/-- If a category has images, equalizers and pullbacks, then images are automatically strong epi
    images. -/
@[priority 100]
instance has_strong_epi_images_of_has_pullbacks_of_has_equalizers [has_pullbacks C]
  [has_equalizers C] : has_strong_epi_images C :=
{ strong_factor_thru_image := λ X Y f,
  { epi := by apply_instance,
    has_lift := λ A B x y h h_mono w, arrow.has_lift.mk
    { lift := image.lift
      { I := pullback h y,
        m := pullback.snd ≫ image.ι f,
        m_mono := by exactI mono_comp _ _,
        e := pullback.lift _ _ w } ≫ pullback.fst } } }

end has_strong_epi_images

variables [has_strong_epi_mono_factorisations.{v} C]
variables {X Y : C} {f : X ⟶ Y}

/--
If `C` has strong epi mono factorisations, then the image is unique up to isomorphism, in that if
`f` factors as a strong epi followed by a mono, this factorisation is essentially the image
factorisation.
-/
def image.iso_strong_epi_mono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [strong_epi e]
  [mono m] :
  I' ≅ image f :=
is_image.iso_ext {strong_epi_mono_factorisation . I := I', m := m, e := e}.to_mono_is_image $
  image.is_image f

@[simp]
lemma image.iso_strong_epi_mono_hom_comp_ι {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
  [strong_epi e] [mono m] :
  (image.iso_strong_epi_mono e m comm).hom ≫ image.ι f = m :=
is_image.lift_fac _ _

@[simp]
lemma image.iso_strong_epi_mono_inv_comp_mono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
  [strong_epi e] [mono m] :
  (image.iso_strong_epi_mono e m comm).inv ≫ m = image.ι f :=
image.lift_fac _

end category_theory.limits
