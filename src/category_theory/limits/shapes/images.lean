/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.limits.shapes.equalizers
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

end is_image

/-- Data exhibiting that a morphism `f` has an image. -/
class has_image (f : X ⟶ Y) :=
(F : mono_factorisation f)
(is_image : is_image F)

section
variable [has_image f]

/-- The chosen factorisation of `f` through a monomorphism. -/
def image.mono_factorisation : mono_factorisation f := has_image.F
/-- The witness of the universal property for the chosen factorisation of `f` through a monomorphism. -/
def image.is_image : is_image (image.mono_factorisation f) := has_image.is_image

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
/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the image. -/
def image.lift (F' : mono_factorisation f) : image f ⟶ F'.I := (image.is_image f).lift F'
@[simp, reassoc]
lemma image.lift_fac (F' : mono_factorisation f) : image.lift F' ≫ F'.m = image.ι f :=
(image.is_image f).lift_fac' F'
@[simp, reassoc]
lemma image.fac_lift (F' : mono_factorisation f) : factor_thru_image f ≫ image.lift F' = F'.e :=
(image.is_image f).fac_lift F'

-- TODO we could put a category structure on `mono_factorisation f`,
-- with the morphisms being `g : I ⟶ I'` commuting with the `m`s
-- (they then automatically commute with the `e`s)
-- and show that an `image_of f` gives an initial object there
-- (uniqueness of the lift comes for free).

instance lift_mono (F' : mono_factorisation f) : mono (image.lift F') :=
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
(cancel_mono F'.m).1 (by simp [w])
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

-- This is the proof from https://en.wikipedia.org/wiki/Image_(category_theory), which is taken from:
-- Mitchell, Barry (1965), Theory of categories, MR 0202787, p.12, Proposition 10.1
instance [Π {Z : C} (g h : image f ⟶ Z), has_limit (parallel_pair g h)] :
  epi (factor_thru_image f) :=
⟨λ Z g h w,
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

lemma epi_of_epi_image {X Y : C} (f : X ⟶ Y) [has_image f]
  [epi (image.ι f)] [epi (factor_thru_image f)] : epi f :=
by { rw [←image.fac f], apply epi_comp, }

end

section
variables {f} {f' : X ⟶ Y} [has_image f] [has_image f']

/-- An equation between morphisms gives a comparison map between the images (which momentarily we prove is an iso). -/
def image.eq_to_hom (h : f = f') : image f ⟶ image f' :=
image.lift
{ I := image f',
  m := image.ι f',
  e := factor_thru_image f', }.

instance (h : f = f') : is_iso (image.eq_to_hom h) :=
{ inv := image.eq_to_hom h.symm,
  hom_inv_id' := (cancel_mono (image.ι f)).1 (by simp [image.eq_to_hom]),
  inv_hom_id' := (cancel_mono (image.ι f')).1 (by simp [image.eq_to_hom]), }

/-- An equation between morphisms gives an isomorphism between the images. -/
def image.eq_to_iso (h : f = f') : image f ≅ image f' := as_iso (image.eq_to_hom h)
end

section
variables {Z : C} (g : Y ⟶ Z)

/-- The comparison map `image (f ≫ g) ⟶ image g`. -/
def image.pre_comp [has_image g] [has_image (f ≫ g)] : image (f ≫ g) ⟶ image g :=
image.lift
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
image.pre_comp f (g ≫ h) ≫ image.pre_comp g h = image.eq_to_hom (category.assoc f g h).symm ≫ (image.pre_comp (f ≫ g) h) :=
begin
  apply (cancel_mono (image.ι h)).1,
  simp [image.pre_comp, image.eq_to_hom],
end

-- Note that in general we don't have the other comparison map you might expect
-- `image f ⟶ image (f ≫ g)`.

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
class has_image_map {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g) :=
(map : image f.hom ⟶ image g.hom)
(map_ι' : map ≫ image.ι g.hom = image.ι f.hom ≫ sq.right . obviously)

restate_axiom has_image_map.map_ι'
attribute [simp, reassoc] has_image_map.map_ι

@[simp, reassoc]
lemma has_image_map.factor_map {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g)
  [has_image_map sq] :
  factor_thru_image f.hom ≫ has_image_map.map sq = sq.left ≫ factor_thru_image g.hom :=
(cancel_mono (image.ι g.hom)).1 $ by simp [arrow.w]

variables {f g : arrow C} [has_image f.hom] [has_image g.hom] (sq : f ⟶ g)

section
local attribute [ext] has_image_map

instance : subsingleton (has_image_map sq) :=
subsingleton.intro $ λ a b, has_image_map.ext a b $ (cancel_mono (image.ι g.hom)).1 $
  by simp only [has_image_map.map_ι]

end

variable [has_image_map sq]

/-- The map on images induced by a commutative square. -/
abbreviation image.map : image f.hom ⟶ image g.hom := has_image_map.map sq

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
def has_image_map_comp : has_image_map (sq ≫ sq') :=
{ map := image.map sq ≫ image.map sq' }

@[simp]
lemma image.map_comp [has_image_map (sq ≫ sq')] :
  image.map (sq ≫ sq') = image.map sq ≫ image.map sq' :=
show (has_image_map.map (sq ≫ sq')) = (has_image_map_comp sq sq').map, by congr

end

section
variables (f)

/-- The identity `image f ⟶ image f` fits into the commutative square represented by the identity
    morphism `𝟙 f` in the arrow category. -/
def has_image_map_id : has_image_map (𝟙 f) :=
{ map := 𝟙 (image f.hom) }

@[simp]
lemma image.map_id [has_image_map (𝟙 f)] : image.map (𝟙 f) = 𝟙 (image f.hom) :=
show (image.map (𝟙 f)) = (has_image_map_id f).map, by congr

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
class has_strong_epi_mono_factorisations :=
(has_fac : Π {X Y : C} (f : X ⟶ Y), strong_epi_mono_factorisation f)

@[priority 100]
instance has_images_of_has_strong_epi_mono_factorisations
  [has_strong_epi_mono_factorisations C] : has_images C :=
{ has_image := λ X Y f,
  let F' := has_strong_epi_mono_factorisations.has_fac f in
  { F := F'.to_mono_factorisation,
    is_image := F'.to_mono_is_image } }

end strong_epi_mono_factorisation

section has_strong_epi_images
variables (C) [has_images C]

/-- A category has strong epi images if it has all images and `factor_thru_image f` is a strong
    epimorphism for all `f`. -/
class has_strong_epi_images :=
(strong_factor_thru_image : Π {X Y : C} (f : X ⟶ Y), strong_epi (factor_thru_image f))

attribute [instance] has_strong_epi_images.strong_factor_thru_image
end has_strong_epi_images

section has_strong_epi_images

/-- If we constructed our images from strong epi-mono factorisations, then these images are
    strong epi images. -/
@[priority 100]
instance has_strong_epi_images_of_has_strong_epi_mono_factorisations
  [has_strong_epi_mono_factorisations C] : has_strong_epi_images C :=
{ strong_factor_thru_image := λ X Y f,
    (has_strong_epi_mono_factorisations.has_fac f).e_strong_epi }

end has_strong_epi_images

section has_strong_epi_images
variables [has_images C]

/-- A category with strong epi images has image maps. The construction is taken from Borceux,
    Handbook of Categorical Algebra 1, Proposition 4.4.5. -/
@[priority 100]
instance has_image_maps_of_has_strong_epi_images [has_strong_epi_images C] :
  has_image_maps C :=
{ has_image_map := λ f g st,
    let I := image (image.ι f.hom ≫ st.right) in
    let I' := image (st.left ≫ factor_thru_image g.hom) in
    let upper : strong_epi_mono_factorisation (f.hom ≫ st.right) :=
    { I := I,
      e := factor_thru_image f.hom ≫ factor_thru_image (image.ι f.hom ≫ st.right),
      m := image.ι (image.ι f.hom ≫ st.right),
      e_strong_epi := strong_epi_comp _ _,
      m_mono := by apply_instance } in
    let lower : strong_epi_mono_factorisation (f.hom ≫ st.right) :=
    { I := I',
      e := factor_thru_image (st.left ≫ factor_thru_image g.hom),
      m := image.ι (st.left ≫ factor_thru_image g.hom) ≫ image.ι g.hom,
      fac' := by simp [arrow.w],
      e_strong_epi := by apply_instance,
      m_mono := mono_comp _ _ } in
    let s : I ⟶ I' := is_image.lift upper.to_mono_is_image lower.to_mono_factorisation in
    { map := factor_thru_image (image.ι f.hom ≫ st.right) ≫ s ≫
        image.ι (st.left ≫ factor_thru_image g.hom),
      map_ι' := by rw [category.assoc, category.assoc,
        is_image.lift_fac upper.to_mono_is_image lower.to_mono_factorisation, image.fac] } }

end has_strong_epi_images

end category_theory.limits
