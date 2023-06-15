/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang
-/
import category_theory.limits.shapes.wide_pullbacks
import category_theory.limits.shapes.binary_products

/-!
# Pullbacks

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define a category `walking_cospan` (resp. `walking_span`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

noncomputable theory

open category_theory

namespace category_theory.limits

universes w v₁ v₂ v u u₂

local attribute [tidy] tactic.case_bash

/--
The type of objects for the diagram indexing a pullback, defined as a special case of
`wide_pullback_shape`.
-/
abbreviation walking_cospan : Type := wide_pullback_shape walking_pair

/-- The left point of the walking cospan. -/
@[pattern] abbreviation walking_cospan.left : walking_cospan := some walking_pair.left
/-- The right point of the walking cospan. -/
@[pattern] abbreviation walking_cospan.right : walking_cospan := some walking_pair.right
/-- The central point of the walking cospan. -/
@[pattern] abbreviation walking_cospan.one : walking_cospan := none

/--
The type of objects for the diagram indexing a pushout, defined as a special case of
`wide_pushout_shape`.
-/
abbreviation walking_span : Type := wide_pushout_shape walking_pair

/-- The left point of the walking span. -/
@[pattern] abbreviation walking_span.left : walking_span := some walking_pair.left
/-- The right point of the walking span. -/
@[pattern] abbreviation walking_span.right : walking_span := some walking_pair.right
/-- The central point of the walking span. -/
@[pattern] abbreviation walking_span.zero : walking_span := none

namespace walking_cospan

/-- The type of arrows for the diagram indexing a pullback. -/
abbreviation hom : walking_cospan → walking_cospan → Type := wide_pullback_shape.hom

/-- The left arrow of the walking cospan. -/
@[pattern] abbreviation hom.inl : left ⟶ one := wide_pullback_shape.hom.term _
/-- The right arrow of the walking cospan. -/
@[pattern] abbreviation hom.inr : right ⟶ one := wide_pullback_shape.hom.term _
/-- The identity arrows of the walking cospan. -/
@[pattern] abbreviation hom.id (X : walking_cospan) : X ⟶ X := wide_pullback_shape.hom.id X

instance (X Y : walking_cospan) : subsingleton (X ⟶ Y) := by tidy

end walking_cospan

namespace walking_span

/-- The type of arrows for the diagram indexing a pushout. -/
abbreviation hom : walking_span → walking_span → Type := wide_pushout_shape.hom

/-- The left arrow of the walking span. -/
@[pattern] abbreviation hom.fst : zero ⟶ left := wide_pushout_shape.hom.init _
/-- The right arrow of the walking span. -/
@[pattern] abbreviation hom.snd : zero ⟶ right := wide_pushout_shape.hom.init _
/-- The identity arrows of the walking span. -/
@[pattern] abbreviation hom.id (X : walking_span) : X ⟶ X := wide_pushout_shape.hom.id X

instance (X Y : walking_span) : subsingleton (X ⟶ Y) := by tidy

end walking_span

open walking_span.hom walking_cospan.hom wide_pullback_shape.hom wide_pushout_shape.hom

variables {C : Type u} [category.{v} C]

/-- To construct an isomorphism of cones over the walking cospan,
it suffices to construct an isomorphism
of the cone points and check it commutes with the legs to `left` and `right`. -/
def walking_cospan.ext {F : walking_cospan ⥤ C} {s t : cone F} (i : s.X ≅ t.X)
  (w₁ : s.π.app walking_cospan.left = i.hom ≫ t.π.app walking_cospan.left)
  (w₂ : s.π.app walking_cospan.right = i.hom ≫ t.π.app walking_cospan.right) :
  s ≅ t :=
begin
  apply cones.ext i,
  rintro (⟨⟩|⟨⟨⟩⟩),
  { have h₁ := s.π.naturality walking_cospan.hom.inl,
    dsimp at h₁, simp only [category.id_comp] at h₁,
    have h₂ := t.π.naturality walking_cospan.hom.inl,
    dsimp at h₂, simp only [category.id_comp] at h₂,
    simp_rw [h₂, ←category.assoc, ←w₁, ←h₁], },
  { exact w₁, },
  { exact w₂, },
end

/-- To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`. -/
def walking_span.ext {F : walking_span ⥤ C} {s t : cocone F} (i : s.X ≅ t.X)
  (w₁ : s.ι.app walking_cospan.left ≫ i.hom = t.ι.app walking_cospan.left)
  (w₂ : s.ι.app walking_cospan.right ≫ i.hom = t.ι.app walking_cospan.right) :
  s ≅ t :=
begin
  apply cocones.ext i,
  rintro (⟨⟩|⟨⟨⟩⟩),
  { have h₁ := s.ι.naturality walking_span.hom.fst,
    dsimp at h₁, simp only [category.comp_id] at h₁,
    have h₂ := t.ι.naturality walking_span.hom.fst,
    dsimp at h₂, simp only [category.comp_id] at h₂,
    simp_rw [←h₁, category.assoc, w₁, h₂], },
  { exact w₁, },
  { exact w₂, },
end

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan ⥤ C :=
wide_pullback_shape.wide_cospan Z
  (λ j, walking_pair.cases_on j X Y) (λ j, walking_pair.cases_on j f g)

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : walking_span ⥤ C :=
wide_pushout_shape.wide_span X
  (λ j, walking_pair.cases_on j Y Z) (λ j, walking_pair.cases_on j f g)

@[simp] lemma cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).obj walking_cospan.left = X := rfl
@[simp] lemma span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).obj walking_span.left = Y := rfl

@[simp] lemma cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).obj walking_cospan.right = Y := rfl
@[simp] lemma span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).obj walking_span.right = Z := rfl

@[simp] lemma cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).obj walking_cospan.one = Z := rfl
@[simp] lemma span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).obj walking_span.zero = X := rfl

@[simp] lemma cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).map walking_cospan.hom.inl = f := rfl
@[simp] lemma span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).map walking_span.hom.fst = f := rfl

@[simp] lemma cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).map walking_cospan.hom.inr = g := rfl
@[simp] lemma span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).map walking_span.hom.snd = g := rfl

lemma cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : walking_cospan) :
  (cospan f g).map (walking_cospan.hom.id w) = 𝟙 _ := rfl
lemma span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : walking_span) :
  (span f g).map (walking_span.hom.id w) = 𝟙 _ := rfl

/-- Every diagram indexing an pullback is naturally isomorphic (actually, equal) to a `cospan` -/
@[simps {rhs_md := semireducible}]
def diagram_iso_cospan (F : walking_cospan ⥤ C) :
  F ≅ cospan (F.map inl) (F.map inr) :=
nat_iso.of_components (λ j, eq_to_iso (by tidy)) (by tidy)

/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
@[simps {rhs_md := semireducible}]
def diagram_iso_span (F : walking_span ⥤ C) :
  F ≅ span (F.map fst) (F.map snd) :=
nat_iso.of_components (λ j, eq_to_iso (by tidy)) (by tidy)

variables {D : Type u₂} [category.{v₂} D]

/-- A functor applied to a cospan is a cospan. -/
def cospan_comp_iso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
nat_iso.of_components (by rintros (⟨⟩|⟨⟨⟩⟩); exact iso.refl _)
  (by rintros (⟨⟩|⟨⟨⟩⟩) (⟨⟩|⟨⟨⟩⟩) ⟨⟩; repeat { dsimp, simp, })

section
variables (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

@[simp] lemma cospan_comp_iso_app_left :
(cospan_comp_iso F f g).app walking_cospan.left = iso.refl _ :=
rfl

@[simp] lemma cospan_comp_iso_app_right :
  (cospan_comp_iso F f g).app walking_cospan.right = iso.refl _ :=
rfl

@[simp] lemma cospan_comp_iso_app_one :
  (cospan_comp_iso F f g).app walking_cospan.one = iso.refl _ :=
rfl

@[simp] lemma cospan_comp_iso_hom_app_left :
  (cospan_comp_iso F f g).hom.app walking_cospan.left = 𝟙 _ :=
rfl

@[simp] lemma cospan_comp_iso_hom_app_right :
  (cospan_comp_iso F f g).hom.app walking_cospan.right = 𝟙 _ :=
rfl

@[simp] lemma cospan_comp_iso_hom_app_one :
  (cospan_comp_iso F f g).hom.app walking_cospan.one = 𝟙 _ :=
rfl

@[simp] lemma cospan_comp_iso_inv_app_left :
  (cospan_comp_iso F f g).inv.app walking_cospan.left = 𝟙 _ :=
rfl

@[simp] lemma cospan_comp_iso_inv_app_right :
  (cospan_comp_iso F f g).inv.app walking_cospan.right = 𝟙 _ :=
rfl

@[simp] lemma cospan_comp_iso_inv_app_one :
  (cospan_comp_iso F f g).inv.app walking_cospan.one = 𝟙 _ :=
rfl

end

/-- A functor applied to a span is a span. -/
def span_comp_iso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  span f g ⋙ F ≅ span (F.map f) (F.map g) :=
nat_iso.of_components (by rintros (⟨⟩|⟨⟨⟩⟩); exact iso.refl _)
  (by rintros (⟨⟩|⟨⟨⟩⟩) (⟨⟩|⟨⟨⟩⟩) ⟨⟩; repeat { dsimp, simp, })

section
variables (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

@[simp] lemma span_comp_iso_app_left : (span_comp_iso F f g).app walking_span.left = iso.refl _ :=
rfl

@[simp] lemma span_comp_iso_app_right : (span_comp_iso F f g).app walking_span.right = iso.refl _ :=
rfl

@[simp] lemma span_comp_iso_app_zero : (span_comp_iso F f g).app walking_span.zero = iso.refl _ :=
rfl

@[simp] lemma span_comp_iso_hom_app_left : (span_comp_iso F f g).hom.app walking_span.left = 𝟙 _ :=
rfl

@[simp] lemma span_comp_iso_hom_app_right :
  (span_comp_iso F f g).hom.app walking_span.right = 𝟙 _ :=
rfl

@[simp] lemma span_comp_iso_hom_app_zero : (span_comp_iso F f g).hom.app walking_span.zero = 𝟙 _ :=
rfl

@[simp] lemma span_comp_iso_inv_app_left : (span_comp_iso F f g).inv.app walking_span.left = 𝟙 _ :=
rfl

@[simp] lemma span_comp_iso_inv_app_right :
  (span_comp_iso F f g).inv.app walking_span.right = 𝟙 _ :=
rfl

@[simp] lemma span_comp_iso_inv_app_zero : (span_comp_iso F f g).inv.app walking_span.zero = 𝟙 _ :=
rfl

end

section
variables {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section
variables {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/-- Construct an isomorphism of cospans from components. -/
def cospan_ext (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom) :
  cospan f g ≅ cospan f' g' :=
nat_iso.of_components (by { rintros (⟨⟩|⟨⟨⟩⟩), exacts [iZ, iX, iY], })
  (by rintros (⟨⟩|⟨⟨⟩⟩) (⟨⟩|⟨⟨⟩⟩) ⟨⟩; repeat { dsimp, simp [wf, wg], })

variables (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)

@[simp] lemma cospan_ext_app_left : (cospan_ext iX iY iZ wf wg).app walking_cospan.left = iX :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_app_right : (cospan_ext iX iY iZ wf wg).app walking_cospan.right = iY :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_app_one : (cospan_ext iX iY iZ wf wg).app walking_cospan.one = iZ :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_hom_app_left :
  (cospan_ext iX iY iZ wf wg).hom.app walking_cospan.left = iX.hom :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_hom_app_right :
  (cospan_ext iX iY iZ wf wg).hom.app walking_cospan.right = iY.hom :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_hom_app_one :
  (cospan_ext iX iY iZ wf wg).hom.app walking_cospan.one = iZ.hom :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_inv_app_left :
  (cospan_ext iX iY iZ wf wg).inv.app walking_cospan.left = iX.inv :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_inv_app_right :
  (cospan_ext iX iY iZ wf wg).inv.app walking_cospan.right = iY.inv :=
by { dsimp [cospan_ext], simp, }

@[simp] lemma cospan_ext_inv_app_one :
  (cospan_ext iX iY iZ wf wg).inv.app walking_cospan.one = iZ.inv :=
by { dsimp [cospan_ext], simp, }

end

section
variables {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

/-- Construct an isomorphism of spans from components. -/
def span_ext (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) :
  span f g ≅ span f' g' :=
nat_iso.of_components (by { rintros (⟨⟩|⟨⟨⟩⟩), exacts [iX, iY, iZ], })
  (by rintros (⟨⟩|⟨⟨⟩⟩) (⟨⟩|⟨⟨⟩⟩) ⟨⟩; repeat { dsimp, simp [wf, wg], })

variables (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)

@[simp] lemma span_ext_app_left : (span_ext iX iY iZ wf wg).app walking_span.left = iY :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_app_right : (span_ext iX iY iZ wf wg).app walking_span.right = iZ :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_app_one : (span_ext iX iY iZ wf wg).app walking_span.zero = iX :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_hom_app_left :
  (span_ext iX iY iZ wf wg).hom.app walking_span.left = iY.hom :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_hom_app_right :
  (span_ext iX iY iZ wf wg).hom.app walking_span.right = iZ.hom :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_hom_app_zero :
  (span_ext iX iY iZ wf wg).hom.app walking_span.zero = iX.hom :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_inv_app_left :
  (span_ext iX iY iZ wf wg).inv.app walking_span.left = iY.inv :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_inv_app_right :
  (span_ext iX iY iZ wf wg).inv.app walking_span.right = iZ.inv :=
by { dsimp [span_ext], simp, }

@[simp] lemma span_ext_inv_app_zero :
  (span_ext iX iY iZ wf wg).inv.app walking_span.zero = iX.inv :=
by { dsimp [span_ext], simp, }

end

end

variables {W X Y Z : C}

/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
    `g : Y ⟶ Z`.-/
abbreviation pullback_cone (f : X ⟶ Z) (g : Y ⟶ Z) := cone (cospan f g)

namespace pullback_cone
variables {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The first projection of a pullback cone. -/
abbreviation fst (t : pullback_cone f g) : t.X ⟶ X := t.π.app walking_cospan.left

/-- The second projection of a pullback cone. -/
abbreviation snd (t : pullback_cone f g) : t.X ⟶ Y := t.π.app walking_cospan.right

@[simp] lemma π_app_left (c : pullback_cone f g) : c.π.app walking_cospan.left = c.fst := rfl

@[simp] lemma π_app_right (c : pullback_cone f g) : c.π.app walking_cospan.right = c.snd := rfl

@[simp] lemma condition_one (t : pullback_cone f g) : t.π.app walking_cospan.one = t.fst ≫ f :=
begin
  have w := t.π.naturality walking_cospan.hom.inl,
  dsimp at w, simpa using w,
end

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit_aux (t : pullback_cone f g) (lift : Π (s : pullback_cone f g), s.X ⟶ t.X)
  (fac_left : ∀ (s : pullback_cone f g), lift s ≫ t.fst = s.fst)
  (fac_right : ∀ (s : pullback_cone f g), lift s ≫ t.snd = s.snd)
  (uniq : ∀ (s : pullback_cone f g) (m : s.X ⟶ t.X)
    (w : ∀ j : walking_cospan, m ≫ t.π.app j = s.π.app j), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j, option.cases_on j
    (by { rw [← s.w inl, ← t.w inl, ←category.assoc], congr, exact fac_left s, } )
    (λ j', walking_pair.cases_on j' (fac_left s) (fac_right s)),
  uniq' := uniq }

/-- This is another convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def is_limit_aux' (t : pullback_cone f g)
  (create : Π (s : pullback_cone f g),
    {l // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd ∧
            ∀ {m}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l}) :
limits.is_limit t :=
pullback_cone.is_limit_aux t
  (λ s, (create s).1)
  (λ s, (create s).2.1)
  (λ s, (create s).2.2.1)
  (λ s m w, (create s).2.2.2 (w walking_cospan.left) (w walking_cospan.right))

/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
    such that `fst ≫ f = snd ≫ g`. -/
@[simps]
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : pullback_cone f g :=
{ X := W,
  π := { app := λ j, option.cases_on j (fst ≫ f) (λ j', walking_pair.cases_on j' fst snd) } }

@[simp] lemma mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).π.app walking_cospan.left = fst := rfl
@[simp] lemma mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).π.app walking_cospan.right = snd := rfl
@[simp] lemma mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).π.app walking_cospan.one = fst ≫ f := rfl

@[simp] lemma mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).fst = fst := rfl
@[simp] lemma mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).snd = snd := rfl

@[reassoc] lemma condition (t : pullback_cone f g) : fst t ≫ f = snd t ≫ g :=
(t.w inl).trans (t.w inr).symm

/-- To check whether a morphism is equalized by the maps of a pullback cone, it suffices to check
  it for `fst t` and `snd t` -/
lemma equalizer_ext (t : pullback_cone f g) {W : C} {k l : W ⟶ t.X}
  (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) :
  ∀ (j : walking_cospan), k ≫ t.π.app j = l ≫ t.π.app j
| (some walking_pair.left) := h₀
| (some walking_pair.right) := h₁
| none := by rw [← t.w inl, reassoc_of h₀]

lemma is_limit.hom_ext {t : pullback_cone f g} (ht : is_limit t) {W : C} {k l : W ⟶ t.X}
  (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
ht.hom_ext $ equalizer_ext _ h₀ h₁

lemma mono_snd_of_is_pullback_of_mono {t : pullback_cone f g} (ht : is_limit t) [mono f] :
  mono t.snd :=
⟨λ W h k i, is_limit.hom_ext ht (by simp [←cancel_mono f, t.condition, reassoc_of i]) i⟩

lemma mono_fst_of_is_pullback_of_mono {t : pullback_cone f g} (ht : is_limit t) [mono g] :
  mono t.fst :=
⟨λ W h k i, is_limit.hom_ext ht i (by simp [←cancel_mono g, ←t.condition, reassoc_of i])⟩

/-- To construct an isomorphism of pullback cones, it suffices to construct an isomorphism
of the cone points and check it commutes with `fst` and `snd`. -/
def ext {s t : pullback_cone f g} (i : s.X ≅ t.X)
  (w₁ : s.fst = i.hom ≫ t.fst) (w₂ : s.snd = i.hom ≫ t.snd) :
  s ≅ t :=
walking_cospan.ext i w₁ w₂

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
    `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.X` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
    -/
def is_limit.lift' {t : pullback_cone f g} (ht : is_limit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
  (w : h ≫ f = k ≫ g) : {l : W ⟶ t.X // l ≫ fst t = h ∧ l ≫ snd t = k} :=
⟨ht.lift $ pullback_cone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩

/--
This is a more convenient formulation to show that a `pullback_cone` constructed using
`pullback_cone.mk` is a limit cone.
-/
def is_limit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
  (lift : Π (s : pullback_cone f g), s.X ⟶ W)
  (fac_left : ∀ (s : pullback_cone f g), lift s ≫ fst = s.fst)
  (fac_right : ∀ (s : pullback_cone f g), lift s ≫ snd = s.snd)
  (uniq : ∀ (s : pullback_cone f g) (m : s.X ⟶ W)
    (w_fst : m ≫ fst = s.fst) (w_snd : m ≫ snd = s.snd), m = lift s) :
  is_limit (mk fst snd eq) :=
is_limit_aux _ lift fac_left fac_right
  (λ s m w, uniq s m (w walking_cospan.left) (w walking_cospan.right))

/-- The flip of a pullback square is a pullback square. -/
def flip_is_limit {W : C} {h : W ⟶ X} {k : W ⟶ Y}
  {comm : h ≫ f = k ≫ g} (t : is_limit (mk _ _ comm.symm)) :
  is_limit (mk _ _ comm) :=
is_limit_aux' _ $ λ s,
begin
  refine ⟨(is_limit.lift' t _ _ s.condition.symm).1,
          (is_limit.lift' t _ _ _).2.2,
          (is_limit.lift' t _ _ _).2.1, λ m m₁ m₂, t.hom_ext _⟩,
  apply (mk k h _).equalizer_ext,
  { rwa (is_limit.lift' t _ _ _).2.1 },
  { rwa (is_limit.lift' t _ _ _).2.2 },
end

/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def is_limit_mk_id_id (f : X ⟶ Y) [mono f] :
  is_limit (mk (𝟙 X) (𝟙 X) rfl : pullback_cone f f) :=
is_limit.mk _
  (λ s, s.fst)
  (λ s, category.comp_id _)
  (λ s, by rw [←cancel_mono f, category.comp_id, s.condition])
  (λ s m m₁ m₂, by simpa using m₁)

/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `pullback_cone.is_id_of_mono`.
-/
lemma mono_of_is_limit_mk_id_id (f : X ⟶ Y)
  (t : is_limit (mk (𝟙 X) (𝟙 X) rfl : pullback_cone f f)) :
  mono f :=
⟨λ Z g h eq, by { rcases pullback_cone.is_limit.lift' t _ _ eq with ⟨_, rfl, rfl⟩, refl } ⟩

/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
    `x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and
    `y`.  -/
def is_limit_of_factors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [mono h]
  (x : X ⟶ W) (y : Y ⟶ W) (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : pullback_cone f g)
  (hs : is_limit s) : is_limit (pullback_cone.mk _ _ (show s.fst ≫ x = s.snd ≫ y,
    from (cancel_mono h).1 $ by simp only [category.assoc, hxh, hyh, s.condition])) :=
pullback_cone.is_limit_aux' _ $ λ t,
  ⟨hs.lift (pullback_cone.mk t.fst t.snd $ by rw [←hxh, ←hyh, reassoc_of t.condition]),
  ⟨hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right, λ r hr hr',
  begin
    apply pullback_cone.is_limit.hom_ext hs;
    simp only [pullback_cone.mk_fst, pullback_cone.mk_snd] at ⊢ hr hr';
    simp only [hr, hr'];
    symmetry,
    exacts [hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right]
  end⟩⟩

/-- If `W` is the pullback of `f, g`,
it is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
def is_limit_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [mono i]
  (s : pullback_cone f g) (H : is_limit s) :
  is_limit (pullback_cone.mk _ _ (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i,
    by rw [← category.assoc, ← category.assoc, s.condition])) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  rcases pullback_cone.is_limit.lift' H s.fst s.snd
    ((cancel_mono i).mp (by simpa using s.condition)) with ⟨l, h₁, h₂⟩,
  refine ⟨l,h₁,h₂,_⟩,
  intros m hm₁ hm₂,
  exact (pullback_cone.is_limit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
end

end pullback_cone

/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
    `g : X ⟶ Z`.-/
abbreviation pushout_cocone (f : X ⟶ Y) (g : X ⟶ Z) := cocone (span f g)

namespace pushout_cocone

variables {f : X ⟶ Y} {g : X ⟶ Z}

/-- The first inclusion of a pushout cocone. -/
abbreviation inl (t : pushout_cocone f g) : Y ⟶ t.X := t.ι.app walking_span.left

/-- The second inclusion of a pushout cocone. -/
abbreviation inr (t : pushout_cocone f g) : Z ⟶ t.X := t.ι.app walking_span.right

@[simp] lemma ι_app_left (c : pushout_cocone f g) : c.ι.app walking_span.left = c.inl := rfl

@[simp] lemma ι_app_right (c : pushout_cocone f g) : c.ι.app walking_span.right = c.inr := rfl

@[simp] lemma condition_zero (t : pushout_cocone f g) : t.ι.app walking_span.zero = f ≫ t.inl :=
begin
  have w := t.ι.naturality walking_span.hom.fst,
  dsimp at w, simpa using w.symm,
end

/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
    It only asks for a proof of facts that carry any mathematical content -/
def is_colimit_aux (t : pushout_cocone f g) (desc : Π (s : pushout_cocone f g), t.X ⟶ s.X)
  (fac_left : ∀ (s : pushout_cocone f g), t.inl ≫ desc s = s.inl)
  (fac_right : ∀ (s : pushout_cocone f g), t.inr ≫ desc s = s.inr)
  (uniq : ∀ (s : pushout_cocone f g) (m : t.X ⟶ s.X)
    (w : ∀ j : walking_span, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
  is_colimit t :=
{ desc := desc,
  fac' := λ s j, option.cases_on j (by { simp [← s.w fst, ← t.w fst, fac_left s] } )
                    (λ j', walking_pair.cases_on j' (fac_left s) (fac_right s)),
  uniq' := uniq }

/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def is_colimit_aux' (t : pushout_cocone f g)
  (create : Π (s : pushout_cocone f g),
    {l // t.inl ≫ l = s.inl ∧ t.inr ≫ l = s.inr ∧
            ∀ {m}, t.inl ≫ m = s.inl → t.inr ≫ m = s.inr → m = l}) :
is_colimit t :=
is_colimit_aux t
  (λ s, (create s).1)
  (λ s, (create s).2.1)
  (λ s, (create s).2.2.1)
  (λ s m w, (create s).2.2.2 (w walking_cospan.left) (w walking_cospan.right))

/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
    that `f ≫ inl = g ↠ inr`. -/
@[simps]
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : pushout_cocone f g :=
{ X := W,
  ι := { app := λ j, option.cases_on j (f ≫ inl) (λ j', walking_pair.cases_on j' inl inr) } }

@[simp] lemma mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).ι.app walking_span.left = inl := rfl
@[simp] lemma mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).ι.app walking_span.right = inr := rfl
@[simp] lemma mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).ι.app walking_span.zero = f ≫ inl := rfl

@[simp] lemma mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).inl = inl := rfl
@[simp] lemma mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).inr = inr := rfl

@[reassoc] lemma condition (t : pushout_cocone f g) : f ≫ (inl t) = g ≫ (inr t) :=
(t.w fst).trans (t.w snd).symm

/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
lemma coequalizer_ext (t : pushout_cocone f g) {W : C} {k l : t.X ⟶ W}
  (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) :
  ∀ (j : walking_span), t.ι.app j ≫ k = t.ι.app j ≫ l
| (some walking_pair.left) := h₀
| (some walking_pair.right) := h₁
| none := by rw [← t.w fst, category.assoc, category.assoc, h₀]

lemma is_colimit.hom_ext {t : pushout_cocone f g} (ht : is_colimit t) {W : C} {k l : t.X ⟶ W}
  (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
ht.hom_ext $ coequalizer_ext _ h₀ h₁

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
    morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.X ⟶ W` such that
    `inl t ≫ l = h` and `inr t ≫ l = k`. -/
def is_colimit.desc' {t : pushout_cocone f g} (ht : is_colimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
  (w : f ≫ h = g ≫ k) : {l : t.X ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
⟨ht.desc $ pushout_cocone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩

lemma epi_inr_of_is_pushout_of_epi {t : pushout_cocone f g} (ht : is_colimit t) [epi f] :
  epi t.inr :=
⟨λ W h k i, is_colimit.hom_ext ht (by simp [←cancel_epi f, t.condition_assoc, i]) i⟩

lemma epi_inl_of_is_pushout_of_epi {t : pushout_cocone f g} (ht : is_colimit t) [epi g] :
  epi t.inl :=
⟨λ W h k i, is_colimit.hom_ext ht i (by simp [←cancel_epi g, ←t.condition_assoc, i])⟩

/-- To construct an isomorphism of pushout cocones, it suffices to construct an isomorphism
of the cocone points and check it commutes with `inl` and `inr`. -/
def ext {s t : pushout_cocone f g} (i : s.X ≅ t.X)
  (w₁ : s.inl ≫ i.hom = t.inl) (w₂ : s.inr ≫ i.hom = t.inr) :
  s ≅ t :=
walking_span.ext i w₁ w₂

/--
This is a more convenient formulation to show that a `pushout_cocone` constructed using
`pushout_cocone.mk` is a colimit cocone.
-/
def is_colimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
  (desc : Π (s : pushout_cocone f g), W ⟶ s.X)
  (fac_left : ∀ (s : pushout_cocone f g), inl ≫ desc s = s.inl)
  (fac_right : ∀ (s : pushout_cocone f g), inr ≫ desc s = s.inr)
  (uniq : ∀ (s : pushout_cocone f g) (m : W ⟶ s.X)
    (w_inl : inl ≫ m = s.inl) (w_inr : inr ≫ m = s.inr), m = desc s) :
  is_colimit (mk inl inr eq) :=
is_colimit_aux _ desc fac_left fac_right
  (λ s m w, uniq s m (w walking_cospan.left) (w walking_cospan.right))

/-- The flip of a pushout square is a pushout square. -/
def flip_is_colimit {W : C} {h : Y ⟶ W} {k : Z ⟶ W}
  {comm : f ≫ h = g ≫ k} (t : is_colimit (mk _ _ comm.symm)) :
  is_colimit (mk _ _ comm) :=
is_colimit_aux' _ $ λ s,
begin
  refine ⟨(is_colimit.desc' t _ _ s.condition.symm).1,
          (is_colimit.desc' t _ _ _).2.2,
          (is_colimit.desc' t _ _ _).2.1, λ m m₁ m₂, t.hom_ext _⟩,
  apply (mk k h _).coequalizer_ext,
  { rwa (is_colimit.desc' t _ _ _).2.1 },
  { rwa (is_colimit.desc' t _ _ _).2.2 },
end

/--
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_is_colimit_mk_id_id`.
-/
def is_colimit_mk_id_id (f : X ⟶ Y) [epi f] :
  is_colimit (mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f) :=
is_colimit.mk _
  (λ s, s.inl)
  (λ s, category.id_comp _)
  (λ s, by rw [←cancel_epi f, category.id_comp, s.condition])
  (λ s m m₁ m₂, by simpa using m₁)

/--
`f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `pushout_cocone.is_colimit_mk_id_id`.
-/
lemma epi_of_is_colimit_mk_id_id (f : X ⟶ Y)
  (t : is_colimit (mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f)) :
  epi f :=
⟨λ Z g h eq, by { rcases pushout_cocone.is_colimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩, refl }⟩

/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
    `x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
    `y`.  -/
def is_colimit_of_factors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [epi h]
  (x : W ⟶ Y) (y : W ⟶ Z) (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : pushout_cocone f g)
  (hs : is_colimit s) : is_colimit (pushout_cocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr,
    from (cancel_epi h).1 $ by rw [reassoc_of hhx, reassoc_of hhy, s.condition])) :=
pushout_cocone.is_colimit_aux' _ $ λ t,
  ⟨hs.desc (pushout_cocone.mk t.inl t.inr $
    by rw [←hhx, ←hhy, category.assoc, category.assoc, t.condition]),
  ⟨hs.fac _ walking_span.left, hs.fac _ walking_span.right, λ r hr hr',
  begin
    apply pushout_cocone.is_colimit.hom_ext hs;
    simp only [pushout_cocone.mk_inl, pushout_cocone.mk_inr] at ⊢ hr hr';
    simp only [hr, hr'];
    symmetry,
    exacts [hs.fac _ walking_span.left, hs.fac _ walking_span.right]
  end⟩⟩

/-- If `W` is the pushout of `f, g`,
it is also the pushout of `h ≫ f, h ≫ g` for any epi `h`. -/
def is_colimit_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [epi h]
  (s : pushout_cocone f g) (H : is_colimit s) :
  is_colimit (pushout_cocone.mk _ _ (show (h ≫ f) ≫ s.inl = (h ≫ g) ≫ s.inr,
    by rw [category.assoc, category.assoc, s.condition])) :=
begin
  apply pushout_cocone.is_colimit_aux',
  intro s,
  rcases pushout_cocone.is_colimit.desc' H s.inl s.inr
    ((cancel_epi h).mp (by simpa using s.condition)) with ⟨l, h₁, h₂⟩,
  refine ⟨l,h₁,h₂,_⟩,
  intros m hm₁ hm₂,
  exact (pushout_cocone.is_colimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
end

end pushout_cocone

/-- This is a helper construction that can be useful when verifying that a category has all
    pullbacks. Given `F : walking_cospan ⥤ C`, which is really the same as
    `cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
    get a cone on `F`.

    If you're thinking about using this, have a look at `has_pullbacks_of_has_limit_cospan`,
    which you may find to be an easier way of achieving your goal. -/
@[simps]
def cone.of_pullback_cone
  {F : walking_cospan ⥤ C} (t : pullback_cone (F.map inl) (F.map inr)) : cone F :=
{ X := t.X,
  π := t.π ≫ (diagram_iso_cospan F).inv }

/-- This is a helper construction that can be useful when verifying that a category has all
    pushout. Given `F : walking_span ⥤ C`, which is really the same as
    `span (F.map fst) (F.mal snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at `has_pushouts_of_has_colimit_span`, which
    you may find to be an easiery way of achieving your goal.  -/
@[simps]
def cocone.of_pushout_cocone
  {F : walking_span ⥤ C} (t : pushout_cocone (F.map fst) (F.map snd)) : cocone F :=
{ X := t.X,
  ι := (diagram_iso_span F).hom ≫ t.ι }

/-- Given `F : walking_cospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
    and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
def pullback_cone.of_cone
  {F : walking_cospan ⥤ C} (t : cone F) : pullback_cone (F.map inl) (F.map inr) :=
{ X := t.X,
  π := t.π ≫ (diagram_iso_cospan F).hom }

/-- A diagram `walking_cospan ⥤ C` is isomorphic to some `pullback_cone.mk` after
composing with `diagram_iso_cospan`. -/
@[simps] def pullback_cone.iso_mk {F : walking_cospan ⥤ C} (t : cone F) :
  (cones.postcompose (diagram_iso_cospan.{v} _).hom).obj t ≅
    pullback_cone.mk (t.π.app walking_cospan.left) (t.π.app walking_cospan.right)
    ((t.π.naturality inl).symm.trans (t.π.naturality inr : _)) :=
cones.ext (iso.refl _) $ by rintro (_|(_|_)); { dsimp, simp }

/-- Given `F : walking_span ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
    and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
def pushout_cocone.of_cocone
  {F : walking_span ⥤ C} (t : cocone F) : pushout_cocone (F.map fst) (F.map snd) :=
{ X := t.X,
  ι := (diagram_iso_span F).inv ≫ t.ι }

/-- A diagram `walking_span ⥤ C` is isomorphic to some `pushout_cocone.mk` after composing with
`diagram_iso_span`. -/
@[simps] def pushout_cocone.iso_mk {F : walking_span ⥤ C} (t : cocone F) :
  (cocones.precompose (diagram_iso_span.{v} _).inv).obj t ≅
    pushout_cocone.mk (t.ι.app walking_span.left) (t.ι.app walking_span.right)
    ((t.ι.naturality fst).trans (t.ι.naturality snd).symm) :=
cocones.ext (iso.refl _) $ by rintro (_|(_|_)); { dsimp, simp }
/--
`has_pullback f g` represents a particular choice of limiting cone
for the pair of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`.
-/
abbreviation has_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) := has_limit (cospan f g)
/--
`has_pushout f g` represents a particular choice of colimiting cocone
for the pair of morphisms `f : X ⟶ Y` and `g : X ⟶ Z`.
-/
abbreviation has_pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) := has_colimit (span f g)

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbreviation pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] :=
limit (cospan f g)
/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbreviation pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_pushout f g] :=
colimit (span f g)

/-- The first projection of the pullback of `f` and `g`. -/
abbreviation pullback.fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] :
  pullback f g ⟶ X :=
limit.π (cospan f g) walking_cospan.left

/-- The second projection of the pullback of `f` and `g`. -/
abbreviation pullback.snd {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] :
  pullback f g ⟶ Y :=
limit.π (cospan f g) walking_cospan.right

/-- The first inclusion into the pushout of `f` and `g`. -/
abbreviation pushout.inl {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] :
  Y ⟶ pushout f g :=
colimit.ι (span f g) walking_span.left

/-- The second inclusion into the pushout of `f` and `g`. -/
abbreviation pushout.inr {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] :
  Z ⟶ pushout f g :=
colimit.ι (span f g) walking_span.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `pullback.lift : W ⟶ pullback f g`. -/
abbreviation pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g]
  (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
limit.lift _ (pullback_cone.mk h k w)

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `pushout.desc : pushout f g ⟶ W`. -/
abbreviation pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g]
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
colimit.desc _ (pushout_cocone.mk h k w)

@[simp]
lemma pullback_cone.fst_colimit_cocone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_limit (cospan f g)] : pullback_cone.fst (limit.cone (cospan f g)) = pullback.fst :=
rfl

@[simp]
lemma pullback_cone.snd_colimit_cocone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_limit (cospan f g)] : pullback_cone.snd (limit.cone (cospan f g)) = pullback.snd :=
rfl

@[simp]
lemma pushout_cocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
  [has_colimit (span f g)] : pushout_cocone.inl (colimit.cocone (span f g)) = pushout.inl :=
rfl

@[simp]
lemma pushout_cocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
  [has_colimit (span f g)] : pushout_cocone.inr (colimit.cocone (span f g)) = pushout.inr :=
rfl

@[simp, reassoc]
lemma pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g]
  (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst = h :=
limit.lift_π _ _

@[simp, reassoc]
lemma pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g]
  (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd = k :=
limit.lift_π _ _

@[simp, reassoc]
lemma pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g]
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl ≫ pushout.desc h k w = h :=
colimit.ι_desc _ _

@[simp, reassoc]
lemma pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g]
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr ≫ pushout.desc h k w = k :=
colimit.ι_desc _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g]
  (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
  {l : W ⟶ pullback f g // l ≫ pullback.fst = h ∧ l ≫ pullback.snd = k} :=
⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `l : pushout f g ⟶ W` such that `pushout.inl ≫ l = h` and `pushout.inr ≫ l = k`. -/
def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g]
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) :
  {l : pushout f g ⟶ W // pushout.inl ≫ l = h ∧ pushout.inr ≫ l = k} :=
⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[reassoc]
lemma pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] :
  (pullback.fst : pullback f g ⟶ X) ≫ f = pullback.snd ≫ g :=
pullback_cone.condition _

@[reassoc]
lemma pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] :
  f ≫ (pushout.inl : Y ⟶ pushout f g) = g ≫ pushout.inr :=
pushout_cocone.condition _

/--
Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

    W  ⟶  Y
      ↘      ↘
        S  ⟶  T
      ↗      ↗
    X  ⟶  Z

-/
abbreviation pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [has_pullback f₁ f₂]
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [has_pullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂)
  (by simp [← eq₁, ← eq₂, pullback.condition_assoc])

/-- The canonical map `X ×ₛ Y ⟶ X ×ₜ Y` given `S ⟶ T`. -/
abbreviation pullback.map_desc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T)
  [has_pullback f g] [has_pullback (f ≫ i) (g ≫ i)] :
  pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (category.id_comp _).symm (category.id_comp _).symm


/--
Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

        W  ⟶  Y
      ↗      ↗
    S  ⟶  T
      ↘      ↘
        X  ⟶  Z

-/
abbreviation pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [has_pushout f₁ f₂]
  (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [has_pushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
pushout.desc (i₁ ≫ pushout.inl) (i₂ ≫ pushout.inr)
  (by { simp only [← category.assoc, eq₁, eq₂], simp [pushout.condition] })

/-- The canonical map `X ⨿ₛ Y ⟶ X ⨿ₜ Y` given `S ⟶ T`. -/
abbreviation pushout.map_lift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T)
  [has_pushout f g] [has_pushout (i ≫ f) (i ≫ g)] :
  pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (category.comp_id _) (category.comp_id _)

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
@[ext] lemma pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g]
  {W : C} {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst = l ≫ pullback.fst)
  (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
limit.hom_ext $ pullback_cone.equalizer_ext _ h₀ h₁

/-- The pullback cone built from the pullback projections is a pullback. -/
def pullback_is_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] :
  is_limit (pullback_cone.mk (pullback.fst : pullback f g ⟶ _) pullback.snd pullback.condition) :=
pullback_cone.is_limit.mk _ (λ s, pullback.lift s.fst s.snd s.condition)
  (by simp) (by simp) (by tidy)

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g]
  [mono g] : mono (pullback.fst : pullback f g ⟶ X) :=
pullback_cone.mono_fst_of_is_pullback_of_mono (limit.is_limit _)

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g]
  [mono f] : mono (pullback.snd : pullback f g ⟶ Y) :=
pullback_cone.mono_snd_of_is_pullback_of_mono (limit.is_limit _)

/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
instance mono_pullback_to_prod {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_binary_product X Y] :
  mono (prod.lift pullback.fst pullback.snd : pullback f g ⟶ _) :=
⟨λ W i₁ i₂ h, begin
  ext,
  { simpa using congr_arg (λ f, f ≫ prod.fst) h },
  { simpa using congr_arg (λ f, f ≫ prod.snd) h }
end⟩

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext] lemma pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g]
  {W : C} {k l : pushout f g ⟶ W} (h₀ : pushout.inl ≫ k = pushout.inl ≫ l)
  (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
colimit.hom_ext $ pushout_cocone.coequalizer_ext _ h₀ h₁

/-- The pushout cocone built from the pushout coprojections is a pushout. -/
def pushout_is_pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_pushout f g] :
  is_colimit (pushout_cocone.mk (pushout.inl : _ ⟶ pushout f g) pushout.inr pushout.condition) :=
pushout_cocone.is_colimit.mk _ (λ s, pushout.desc s.inl s.inr s.condition)
  (by simp) (by simp) (by tidy)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi g] :
  epi (pushout.inl : Y ⟶ pushout f g) :=
pushout_cocone.epi_inl_of_is_pushout_of_epi (colimit.is_colimit _)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi f] :
  epi (pushout.inr : Z ⟶ pushout f g) :=
pushout_cocone.epi_inr_of_is_pushout_of_epi (colimit.is_colimit _)

/-- The map ` X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
instance epi_coprod_to_pushout {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  [has_pushout f g] [has_binary_coproduct Y Z] :
  epi (coprod.desc pushout.inl pushout.inr : _ ⟶ pushout f g) :=
⟨λ W i₁ i₂ h, begin
  ext,
  { simpa using congr_arg (λ f, coprod.inl ≫ f) h },
  { simpa using congr_arg (λ f, coprod.inr ≫ f) h }
end⟩

instance pullback.map_is_iso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [has_pullback f₁ f₂]
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [has_pullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [is_iso i₁] [is_iso i₂] [is_iso i₃] :
  is_iso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
begin
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩,
  { rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc] },
  { rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc] },
  tidy
end

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps hom]
def pullback.congr_hom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
  (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
  pullback f₁ g₁ ≅ pullback f₂ g₂ :=
as_iso $ pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

@[simp]
lemma pullback.congr_hom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
  (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
  (pullback.congr_hom h₁ h₂).inv =
    pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) :=
begin
  apply pullback.hom_ext,
  { erw pullback.lift_fst,
    rw iso.inv_comp_eq,
    erw pullback.lift_fst_assoc,
    rw [category.comp_id, category.comp_id] },
  { erw pullback.lift_snd,
    rw iso.inv_comp_eq,
    erw pullback.lift_snd_assoc,
    rw [category.comp_id, category.comp_id] },
end

instance pushout.map_is_iso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [has_pushout f₁ f₂]
  (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [has_pushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
  (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [is_iso i₁] [is_iso i₂] [is_iso i₃] :
  is_iso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
begin
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩,
  { rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc] },
  { rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc] },
  tidy
end

lemma pullback.map_desc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)
  (i' : S ⟶ S') [has_pullback f g] [has_pullback (f ≫ i) (g ≫ i)]
  [has_pullback (f ≫ i ≫ i') (g ≫ i ≫ i')] [has_pullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
  pullback.map_desc f g (i ≫ i') = pullback.map_desc f g i ≫ pullback.map_desc _ _ i' ≫
    (pullback.congr_hom (category.assoc _ _ _) (category.assoc _ _ _)).hom :=
by { ext; simp }

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps hom]
def pushout.congr_hom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z}
  (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [has_pushout f₁ g₁] [has_pushout f₂ g₂] :
  pushout f₁ g₁ ≅ pushout f₂ g₂ :=
as_iso $ pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

@[simp]
lemma pushout.congr_hom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z}
  (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [has_pushout f₁ g₁] [has_pushout f₂ g₂] :
  (pushout.congr_hom h₁ h₂).inv =
    pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) :=
begin
  apply pushout.hom_ext,
  { erw pushout.inl_desc,
    rw [iso.comp_inv_eq, category.id_comp],
    erw pushout.inl_desc,
    rw category.id_comp },
  { erw pushout.inr_desc,
    rw [iso.comp_inv_eq, category.id_comp],
    erw pushout.inr_desc,
    rw category.id_comp }
end

lemma pushout.map_lift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T)
  (i' : S' ⟶ S) [has_pushout f g] [has_pushout (i ≫ f) (i ≫ g)]
  [has_pushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)] [has_pushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
  pushout.map_lift f g (i' ≫ i) =
    (pushout.congr_hom (category.assoc _ _ _) (category.assoc _ _ _)).hom ≫
    pushout.map_lift _ _ i' ≫ pushout.map_lift f g i :=
by { ext; simp }

section

variables (G : C ⥤ D)

/--
The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pullback_comparison (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_pullback (G.map f) (G.map g)] :
  G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
pullback.lift (G.map pullback.fst) (G.map pullback.snd)
  (by simp only [←G.map_comp, pullback.condition])

@[simp, reassoc]
lemma pullback_comparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_pullback (G.map f) (G.map g)] :
  pullback_comparison G f g ≫ pullback.fst = G.map pullback.fst :=
pullback.lift_fst _ _ _

@[simp, reassoc]
lemma pullback_comparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_pullback (G.map f) (G.map g)] :
  pullback_comparison G f g ≫ pullback.snd = G.map pullback.snd :=
pullback.lift_snd _ _ _

@[simp, reassoc]
lemma map_lift_pullback_comparison (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_pullback (G.map f) (G.map g)]
  {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullback_comparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [←G.map_comp, w]) :=
by { ext; simp [← G.map_comp] }

/--
The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pushout_comparison (f : X ⟶ Y) (g : X ⟶ Z)
  [has_pushout f g] [has_pushout (G.map f) (G.map g)] :
  pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
pushout.desc (G.map pushout.inl) (G.map pushout.inr)
  (by simp only [←G.map_comp, pushout.condition])

@[simp, reassoc]
lemma inl_comp_pushout_comparison (f : X ⟶ Y) (g : X ⟶ Z)
  [has_pushout f g] [has_pushout (G.map f) (G.map g)] :
  pushout.inl ≫ pushout_comparison G f g = G.map pushout.inl :=
pushout.inl_desc _ _ _

@[simp, reassoc]
lemma inr_comp_pushout_comparison (f : X ⟶ Y) (g : X ⟶ Z)
  [has_pushout f g] [has_pushout (G.map f) (G.map g)] :
  pushout.inr ≫ pushout_comparison G f g = G.map pushout.inr :=
pushout.inr_desc _ _ _

@[simp, reassoc]
lemma pushout_comparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z)
  [has_pushout f g] [has_pushout (G.map f) (G.map g)]
  {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushout_comparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [←G.map_comp, w]) :=
by { ext; simp [← G.map_comp] }

end

section pullback_symmetry

open walking_cospan

variables (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
lemma has_pullback_symmetry [has_pullback f g] : has_pullback g f :=
⟨⟨⟨pullback_cone.mk _ _ pullback.condition.symm,
  pullback_cone.flip_is_limit (pullback_is_pullback _ _)⟩⟩⟩

local attribute [instance] has_pullback_symmetry

/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
def pullback_symmetry [has_pullback f g] :
  pullback f g ≅ pullback g f :=
is_limit.cone_point_unique_up_to_iso
  (pullback_cone.flip_is_limit (pullback_is_pullback f g) :
    is_limit (pullback_cone.mk _ _ pullback.condition.symm))
  (limit.is_limit _)

@[simp, reassoc] lemma pullback_symmetry_hom_comp_fst [has_pullback f g] :
  (pullback_symmetry f g).hom ≫ pullback.fst = pullback.snd := by simp [pullback_symmetry]

@[simp, reassoc] lemma pullback_symmetry_hom_comp_snd [has_pullback f g] :
  (pullback_symmetry f g).hom ≫ pullback.snd = pullback.fst := by simp [pullback_symmetry]

@[simp, reassoc] lemma pullback_symmetry_inv_comp_fst [has_pullback f g] :
  (pullback_symmetry f g).inv ≫ pullback.fst = pullback.snd := by simp [iso.inv_comp_eq]

@[simp, reassoc] lemma pullback_symmetry_inv_comp_snd [has_pullback f g] :
  (pullback_symmetry f g).inv ≫ pullback.snd = pullback.fst := by simp [iso.inv_comp_eq]

end pullback_symmetry

section pushout_symmetry

open walking_cospan

variables (f : X ⟶ Y) (g : X ⟶ Z)

/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
lemma has_pushout_symmetry [has_pushout f g] : has_pushout g f :=
⟨⟨⟨pushout_cocone.mk _ _ pushout.condition.symm,
  pushout_cocone.flip_is_colimit (pushout_is_pushout _ _)⟩⟩⟩

local attribute [instance] has_pushout_symmetry

/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
def pushout_symmetry [has_pushout f g] :
  pushout f g ≅ pushout g f :=
is_colimit.cocone_point_unique_up_to_iso
  (pushout_cocone.flip_is_colimit (pushout_is_pushout f g) :
    is_colimit (pushout_cocone.mk _ _ pushout.condition.symm))
  (colimit.is_colimit _)

@[simp, reassoc] lemma inl_comp_pushout_symmetry_hom [has_pushout f g] :
  pushout.inl ≫ (pushout_symmetry f g).hom = pushout.inr :=
(colimit.is_colimit (span f g)).comp_cocone_point_unique_up_to_iso_hom
  (pushout_cocone.flip_is_colimit (pushout_is_pushout g f)) _

@[simp, reassoc] lemma inr_comp_pushout_symmetry_hom [has_pushout f g] :
  pushout.inr ≫ (pushout_symmetry f g).hom = pushout.inl :=
(colimit.is_colimit (span f g)).comp_cocone_point_unique_up_to_iso_hom
  (pushout_cocone.flip_is_colimit (pushout_is_pushout g f)) _

@[simp, reassoc] lemma inl_comp_pushout_symmetry_inv [has_pushout f g] :
  pushout.inl ≫ (pushout_symmetry f g).inv = pushout.inr := by simp [iso.comp_inv_eq]

@[simp, reassoc] lemma inr_comp_pushout_symmetry_inv [has_pushout f g] :
  pushout.inr ≫ (pushout_symmetry f g).inv = pushout.inl := by simp [iso.comp_inv_eq]

end pushout_symmetry

section pullback_left_iso

open walking_cospan

/-- The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
noncomputable
def pullback_is_pullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z)
  [mono i] [has_pullback f g] :
  is_limit (pullback_cone.mk pullback.fst pullback.snd _) :=
pullback_cone.is_limit_of_comp_mono f g i _ (limit.is_limit (cospan f g))

instance has_pullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z)
  [mono i] [has_pullback f g] : has_pullback (f ≫ i) (g ≫ i) :=
⟨⟨⟨_,pullback_is_pullback_of_comp_mono f g i⟩⟩⟩

variables (f : X ⟶ Z) (g : Y ⟶ Z) [is_iso f]

/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
def pullback_cone_of_left_iso : pullback_cone f g :=
pullback_cone.mk (g ≫ inv f) (𝟙 _) $ by simp

@[simp] lemma pullback_cone_of_left_iso_X :
  (pullback_cone_of_left_iso f g).X = Y := rfl

@[simp] lemma pullback_cone_of_left_iso_fst :
  (pullback_cone_of_left_iso f g).fst = g ≫ inv f := rfl

@[simp] lemma pullback_cone_of_left_iso_snd :
  (pullback_cone_of_left_iso f g).snd = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_left_iso_π_app_none :
  (pullback_cone_of_left_iso f g).π.app none = g := by { delta pullback_cone_of_left_iso, simp }

@[simp] lemma pullback_cone_of_left_iso_π_app_left :
  (pullback_cone_of_left_iso f g).π.app left = g ≫ inv f := rfl

@[simp] lemma pullback_cone_of_left_iso_π_app_right :
  (pullback_cone_of_left_iso f g).π.app right = 𝟙 _ := rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullback_cone_of_left_iso_is_limit :
  is_limit (pullback_cone_of_left_iso f g) :=
pullback_cone.is_limit_aux' _ (λ s, ⟨s.snd, by simp [← s.condition_assoc]⟩)

lemma has_pullback_of_left_iso : has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_left_iso_is_limit f g⟩⟩⟩

local attribute [instance] has_pullback_of_left_iso

instance pullback_snd_iso_of_left_iso : is_iso (pullback.snd : pullback f g ⟶ _) :=
begin
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), _, by simp⟩⟩,
  ext,
  { simp [← pullback.condition_assoc] },
  { simp [pullback.condition_assoc] },
end

variables (i : Z ⟶ W) [mono i]

instance has_pullback_of_right_factors_mono (f : X ⟶ Z) : has_pullback i (f ≫ i) :=
by { conv { congr, rw ←category.id_comp i, }, apply_instance }

instance pullback_snd_iso_of_right_factors_mono (f : X ⟶ Z) :
  is_iso (pullback.snd : pullback i (f ≫ i) ⟶ _) :=
begin
  convert (congr_arg is_iso (show _ ≫ pullback.snd = _,
    from limit.iso_limit_cone_hom_π ⟨_,pullback_is_pullback_of_comp_mono (𝟙 _) f i⟩
      walking_cospan.right)).mp infer_instance;
    exact (category.id_comp _).symm
end

end pullback_left_iso

section pullback_right_iso

open walking_cospan

variables (f : X ⟶ Z) (g : Y ⟶ Z) [is_iso g]

/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
def pullback_cone_of_right_iso : pullback_cone f g :=
pullback_cone.mk (𝟙 _) (f ≫ inv g) $ by simp

@[simp] lemma pullback_cone_of_right_iso_X :
  (pullback_cone_of_right_iso f g).X = X := rfl

@[simp] lemma pullback_cone_of_right_iso_fst :
  (pullback_cone_of_right_iso f g).fst = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_right_iso_snd :
  (pullback_cone_of_right_iso f g).snd = f ≫ inv g := rfl

@[simp] lemma pullback_cone_of_right_iso_π_app_none :
  (pullback_cone_of_right_iso f g).π.app none = f := category.id_comp _

@[simp] lemma pullback_cone_of_right_iso_π_app_left :
  (pullback_cone_of_right_iso f g).π.app left = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_right_iso_π_app_right :
  (pullback_cone_of_right_iso f g).π.app right = f ≫ inv g := rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullback_cone_of_right_iso_is_limit :
  is_limit (pullback_cone_of_right_iso f g) :=
pullback_cone.is_limit_aux' _ (λ s, ⟨s.fst, by simp [s.condition_assoc]⟩)

lemma has_pullback_of_right_iso : has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_right_iso_is_limit f g⟩⟩⟩

local attribute [instance] has_pullback_of_right_iso

instance pullback_snd_iso_of_right_iso : is_iso (pullback.fst : pullback f g ⟶ _) :=
begin
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), _, by simp⟩⟩,
  ext,
  { simp },
  { simp [pullback.condition_assoc] },
end

variables (i : Z ⟶ W) [mono i]

instance has_pullback_of_left_factors_mono (f : X ⟶ Z) : has_pullback (f ≫ i) i :=
by { conv { congr, skip, rw ←category.id_comp i, }, apply_instance }

instance pullback_snd_iso_of_left_factors_mono (f : X ⟶ Z) :
  is_iso (pullback.fst : pullback (f ≫ i) i ⟶ _) :=
begin
  convert (congr_arg is_iso (show _ ≫ pullback.fst = _,
    from limit.iso_limit_cone_hom_π ⟨_,pullback_is_pullback_of_comp_mono f (𝟙 _) i⟩
      walking_cospan.left)).mp infer_instance;
    exact (category.id_comp _).symm
end

end pullback_right_iso

section pushout_left_iso

open walking_span

/-- The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`. -/
noncomputable
def pushout_is_pushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X)
  [epi h] [has_pushout f g] :
  is_colimit (pushout_cocone.mk pushout.inl pushout.inr _) :=
pushout_cocone.is_colimit_of_epi_comp f g h _ (colimit.is_colimit (span f g))

instance has_pushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X)
  [epi h] [has_pushout f g] : has_pushout (h ≫ f) (h ≫ g) :=
⟨⟨⟨_,pushout_is_pushout_of_epi_comp f g h⟩⟩⟩

variables (f : X ⟶ Y) (g : X ⟶ Z) [is_iso f]

/-- If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone. -/
def pushout_cocone_of_left_iso : pushout_cocone f g :=
pushout_cocone.mk (inv f ≫ g) (𝟙 _) $ by simp

@[simp] lemma pushout_cocone_of_left_iso_X :
  (pushout_cocone_of_left_iso f g).X = Z := rfl

@[simp] lemma pushout_cocone_of_left_iso_inl :
  (pushout_cocone_of_left_iso f g).inl = inv f ≫ g := rfl

@[simp] lemma pushout_cocone_of_left_iso_inr :
  (pushout_cocone_of_left_iso f g).inr = 𝟙 _ := rfl

@[simp] lemma pushout_cocone_of_left_iso_ι_app_none :
  (pushout_cocone_of_left_iso f g).ι.app none = g := by { delta pushout_cocone_of_left_iso, simp }

@[simp] lemma pushout_cocone_of_left_iso_ι_app_left :
  (pushout_cocone_of_left_iso f g).ι.app left = inv f ≫ g := rfl

@[simp] lemma pushout_cocone_of_left_iso_ι_app_right :
  (pushout_cocone_of_left_iso f g).ι.app right = 𝟙 _ := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushout_cocone_of_left_iso_is_limit :
  is_colimit (pushout_cocone_of_left_iso f g) :=
pushout_cocone.is_colimit_aux' _ (λ s, ⟨s.inr, by simp [← s.condition]⟩)

lemma has_pushout_of_left_iso : has_pushout f g :=
⟨⟨⟨_, pushout_cocone_of_left_iso_is_limit f g⟩⟩⟩

local attribute [instance] has_pushout_of_left_iso

instance pushout_inr_iso_of_left_iso : is_iso (pushout.inr : _ ⟶ pushout f g) :=
begin
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), (by simp), _⟩⟩,
  ext,
  { simp [← pushout.condition] },
  { simp [pushout.condition_assoc] },
end

variables (h : W ⟶ X) [epi h]

instance has_pushout_of_right_factors_epi (f : X ⟶ Y) : has_pushout h (h ≫ f) :=
by { conv { congr, rw ←category.comp_id h, }, apply_instance }

instance pushout_inr_iso_of_right_factors_epi (f : X ⟶ Y) :
  is_iso (pushout.inr : _ ⟶ pushout h (h ≫ f)) :=
begin
  convert (congr_arg is_iso (show pushout.inr ≫ _ = _,
    from colimit.iso_colimit_cocone_ι_inv ⟨_, pushout_is_pushout_of_epi_comp (𝟙 _) f h⟩
      walking_span.right)).mp infer_instance;
    exact (category.comp_id _).symm
end

end pushout_left_iso

section pushout_right_iso

open walking_span

variables (f : X ⟶ Y) (g : X ⟶ Z) [is_iso g]

/-- If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone. -/
def pushout_cocone_of_right_iso : pushout_cocone f g :=
pushout_cocone.mk (𝟙 _) (inv g ≫ f) $ by simp

@[simp] lemma pushout_cocone_of_right_iso_X :
  (pushout_cocone_of_right_iso f g).X = Y := rfl

@[simp] lemma pushout_cocone_of_right_iso_inl :
  (pushout_cocone_of_right_iso f g).inl = 𝟙 _ := rfl

@[simp] lemma pushout_cocone_of_right_iso_inr :
  (pushout_cocone_of_right_iso f g).inr = inv g ≫ f := rfl

@[simp] lemma pushout_cocone_of_right_iso_ι_app_none :
  (pushout_cocone_of_right_iso f g).ι.app none = f := by { delta pushout_cocone_of_right_iso, simp }

@[simp] lemma pushout_cocone_of_right_iso_ι_app_left :
  (pushout_cocone_of_right_iso f g).ι.app left = 𝟙 _ := rfl

@[simp] lemma pushout_cocone_of_right_iso_ι_app_right :
  (pushout_cocone_of_right_iso f g).ι.app right = inv g ≫ f := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushout_cocone_of_right_iso_is_limit :
  is_colimit (pushout_cocone_of_right_iso f g) :=
pushout_cocone.is_colimit_aux' _ (λ s, ⟨s.inl, by simp [←s.condition]⟩)

lemma has_pushout_of_right_iso : has_pushout f g :=
⟨⟨⟨_, pushout_cocone_of_right_iso_is_limit f g⟩⟩⟩

local attribute [instance] has_pushout_of_right_iso

instance pushout_inl_iso_of_right_iso : is_iso (pushout.inl : _ ⟶ pushout f g) :=
begin
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), (by simp), _⟩⟩,
  ext,
  { simp [←pushout.condition] },
  { simp [pushout.condition] },
end

variables (h : W ⟶ X) [epi h]

instance has_pushout_of_left_factors_epi (f : X ⟶ Y) : has_pushout (h ≫ f) h :=
by { conv { congr, skip, rw ←category.comp_id h, }, apply_instance }

instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
  is_iso (pushout.inl : _ ⟶ pushout (h ≫ f) h) :=
begin
  convert (congr_arg is_iso (show pushout.inl ≫ _ = _,
    from colimit.iso_colimit_cocone_ι_inv ⟨_, pushout_is_pushout_of_epi_comp f (𝟙 _) h⟩
      walking_span.left)).mp infer_instance;
    exact (category.comp_id _).symm
end

end pushout_right_iso

section

open walking_cospan

variable (f : X ⟶ Y)

instance has_kernel_pair_of_mono [mono f] : has_pullback f f :=
⟨⟨⟨_, pullback_cone.is_limit_mk_id_id f⟩⟩⟩

lemma fst_eq_snd_of_mono_eq [mono f] : (pullback.fst : pullback f f ⟶ _) = pullback.snd :=
((pullback_cone.is_limit_mk_id_id f).fac (get_limit_cone (cospan f f)).cone left).symm.trans
  ((pullback_cone.is_limit_mk_id_id f).fac (get_limit_cone (cospan f f)).cone right : _)

@[simp] lemma pullback_symmetry_hom_of_mono_eq [mono f] :
  (pullback_symmetry f f).hom = 𝟙 _ := by ext; simp [fst_eq_snd_of_mono_eq]

instance fst_iso_of_mono_eq [mono f] : is_iso (pullback.fst : pullback f f ⟶ _) :=
begin
  refine ⟨⟨pullback.lift (𝟙 _) (𝟙 _) (by simp), _, by simp⟩⟩,
  ext,
  { simp },
  { simp [fst_eq_snd_of_mono_eq] }
end

instance snd_iso_of_mono_eq [mono f] : is_iso (pullback.snd : pullback f f ⟶ _) :=
by { rw ← fst_eq_snd_of_mono_eq, apply_instance }

end

section

open walking_span

variable (f : X ⟶ Y)

instance has_cokernel_pair_of_epi [epi f] : has_pushout f f :=
⟨⟨⟨_, pushout_cocone.is_colimit_mk_id_id f⟩⟩⟩

lemma inl_eq_inr_of_epi_eq [epi f] : (pushout.inl : _ ⟶ pushout f f) = pushout.inr :=
((pushout_cocone.is_colimit_mk_id_id f).fac
    (get_colimit_cocone (span f f)).cocone left).symm.trans
  ((pushout_cocone.is_colimit_mk_id_id f).fac
    (get_colimit_cocone (span f f)).cocone right : _)

@[simp] lemma pullback_symmetry_hom_of_epi_eq [epi f] :
  (pushout_symmetry f f).hom = 𝟙 _ := by ext; simp [inl_eq_inr_of_epi_eq]

instance inl_iso_of_epi_eq [epi f] : is_iso (pushout.inl : _ ⟶ pushout f f) :=
begin
  refine ⟨⟨pushout.desc (𝟙 _) (𝟙 _) (by simp), by simp, _⟩⟩,
  ext,
  { simp },
  { simp [inl_eq_inr_of_epi_eq] }
end

instance inr_iso_of_epi_eq [epi f] : is_iso (pushout.inr : _ ⟶ pushout f f) :=
by { rw ← inl_eq_inr_of_epi_eq, apply_instance }

end

section paste_lemma

variables {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
variables (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
variables (h₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = f₂ ≫ i₃)

/--
Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pullback if both the small squares are.
-/
def big_square_is_pullback (H : is_limit (pullback_cone.mk _ _ h₂))
  (H' : is_limit (pullback_cone.mk _ _ h₁)) :
  is_limit (pullback_cone.mk _ _ (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃,
      by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
begin
  fapply pullback_cone.is_limit_aux',
  intro s,
  have : (s.fst ≫ g₁) ≫ g₂ = s.snd ≫ i₃ := by rw [← s.condition, category.assoc],
  rcases pullback_cone.is_limit.lift' H (s.fst ≫ g₁) s.snd this with ⟨l₁, hl₁, hl₁'⟩,
  rcases pullback_cone.is_limit.lift' H' s.fst l₁ hl₁.symm with ⟨l₂, hl₂, hl₂'⟩,
  use l₂,
  use hl₂,
  use show l₂ ≫ f₁ ≫ f₂ = s.snd, by { rw [← hl₁', ← hl₂', category.assoc], refl },
  intros m hm₁ hm₂,
  apply pullback_cone.is_limit.hom_ext H',
  { erw [hm₁, hl₂] },
  { apply pullback_cone.is_limit.hom_ext H,
    { erw [category.assoc, ← h₁, ← category.assoc, hm₁, ← hl₂,
      category.assoc, category.assoc, h₁], refl },
    { erw [category.assoc, hm₂, ← hl₁', ← hl₂'] } }
end

/--
Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pushout if both the small squares are.
-/
def big_square_is_pushout (H : is_colimit (pushout_cocone.mk _ _ h₂))
  (H' : is_colimit (pushout_cocone.mk _ _ h₁)) :
  is_colimit (pushout_cocone.mk _ _ (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃,
      by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
begin
  fapply pushout_cocone.is_colimit_aux',
  intro s,
  have : i₁ ≫ s.inl = f₁ ≫ (f₂ ≫ s.inr) := by rw [s.condition, category.assoc],
  rcases pushout_cocone.is_colimit.desc' H' s.inl (f₂ ≫ s.inr) this with ⟨l₁, hl₁, hl₁'⟩,
  rcases pushout_cocone.is_colimit.desc' H l₁ s.inr hl₁' with ⟨l₂, hl₂, hl₂'⟩,
  use l₂,
  use show (g₁ ≫ g₂) ≫ l₂ = s.inl, by { rw [← hl₁, ← hl₂, category.assoc], refl },
  use hl₂',
  intros m hm₁ hm₂,
  apply pushout_cocone.is_colimit.hom_ext H,
  { apply pushout_cocone.is_colimit.hom_ext H',
    { erw [← category.assoc, hm₁, hl₂, hl₁] },
    { erw [← category.assoc, h₂, category.assoc, hm₂, ← hl₂',
      ← category.assoc, ← category.assoc, ← h₂], refl } },
  { erw [hm₂, hl₂'] }
end

/--
Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the left square is a pullback if the right square and the big square are.
-/
def left_square_is_pullback (H : is_limit (pullback_cone.mk _ _ h₂))
  (H' : is_limit (pullback_cone.mk _ _ (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃,
      by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
  is_limit (pullback_cone.mk _ _ h₁) :=
begin
  fapply pullback_cone.is_limit_aux',
  intro s,
  have : s.fst ≫ g₁ ≫ g₂ = (s.snd ≫ f₂) ≫ i₃ :=
  by { rw [← category.assoc, s.condition, category.assoc, category.assoc, h₂] },
  rcases pullback_cone.is_limit.lift' H' s.fst (s.snd ≫ f₂) this with ⟨l₁, hl₁, hl₁'⟩,
  use l₁,
  use hl₁,
  split,
  { apply pullback_cone.is_limit.hom_ext H,
    { erw [category.assoc, ← h₁, ← category.assoc, hl₁, s.condition], refl },
    { erw [category.assoc, hl₁'], refl } },
  { intros m hm₁ hm₂,
    apply pullback_cone.is_limit.hom_ext H',
    { erw [hm₁, hl₁] },
    { erw [hl₁', ← hm₂], exact (category.assoc _ _ _).symm } }
end

/--
Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
def right_square_is_pushout (H : is_colimit (pushout_cocone.mk _ _ h₁))
  (H' : is_colimit (pushout_cocone.mk _ _ (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃,
      by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
  is_colimit (pushout_cocone.mk _ _ h₂) :=
begin
  fapply pushout_cocone.is_colimit_aux',
  intro s,
  have : i₁ ≫ g₁ ≫ s.inl = (f₁ ≫ f₂) ≫ s.inr :=
  by { rw [category.assoc, ← s.condition, ← category.assoc, ← category.assoc, h₁] },
  rcases pushout_cocone.is_colimit.desc' H' (g₁ ≫ s.inl) s.inr this with ⟨l₁, hl₁, hl₁'⟩,
  dsimp at *,
  use l₁,
  refine ⟨_,_,_⟩,
  { apply pushout_cocone.is_colimit.hom_ext H,
    { erw [← category.assoc, hl₁], refl },
    { erw [← category.assoc, h₂, category.assoc, hl₁', s.condition] } },
  { exact hl₁' },
  { intros m hm₁ hm₂,
    apply pushout_cocone.is_colimit.hom_ext H',
    { erw [hl₁, category.assoc, hm₁] },
    { erw [hm₂, hl₁'] } }
end

end paste_lemma

section

variables (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)
variables [has_pullback f g] [has_pullback f' (pullback.fst : pullback f g ⟶ _)]
variables [has_pullback (f' ≫ f) g]

/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
noncomputable
def pullback_right_pullback_fst_iso :
  pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g :=
begin
  let := big_square_is_pullback
    (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _) pullback.snd
    f' f pullback.fst pullback.fst g pullback.condition pullback.condition
    (pullback_is_pullback _ _) (pullback_is_pullback _ _),
  exact (this.cone_point_unique_up_to_iso (pullback_is_pullback _ _) : _)
end

@[simp, reassoc]
lemma pullback_right_pullback_fst_iso_hom_fst :
  (pullback_right_pullback_fst_iso f g f').hom ≫ pullback.fst = pullback.fst :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.left

@[simp, reassoc]
lemma pullback_right_pullback_fst_iso_hom_snd :
  (pullback_right_pullback_fst_iso f g f').hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right

@[simp, reassoc]
lemma pullback_right_pullback_fst_iso_inv_fst :
  (pullback_right_pullback_fst_iso f g f').inv ≫ pullback.fst = pullback.fst :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left

@[simp, reassoc]
lemma pullback_right_pullback_fst_iso_inv_snd_snd :
  (pullback_right_pullback_fst_iso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.right

@[simp, reassoc]
lemma pullback_right_pullback_fst_iso_inv_snd_fst :
  (pullback_right_pullback_fst_iso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' :=
begin
  rw ← pullback.condition,
  exact pullback_right_pullback_fst_iso_inv_fst_assoc _ _ _ _
end

end

section

variables (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)
variables [has_pushout f g] [has_pushout (pushout.inr : _ ⟶ pushout f g) g']
variables [has_pushout f (g ≫ g')]

/-- The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ×[X] W` -/
noncomputable
def pushout_left_pushout_inr_iso :
  pushout (pushout.inr : _ ⟶ pushout f g) g' ≅ pushout f (g ≫ g') :=
((big_square_is_pushout g g' _ _ f _ _ pushout.condition pushout.condition
  (pushout_is_pushout _ _) (pushout_is_pushout _ _))
  .cocone_point_unique_up_to_iso (pushout_is_pushout _ _) : _)

@[simp, reassoc]
lemma inl_pushout_left_pushout_inr_iso_inv :
  pushout.inl ≫ (pushout_left_pushout_inr_iso f g g').inv = pushout.inl ≫ pushout.inl :=
((big_square_is_pushout g g' _ _ f _ _ pushout.condition pushout.condition
  (pushout_is_pushout _ _) (pushout_is_pushout _ _))
  .comp_cocone_point_unique_up_to_iso_inv (pushout_is_pushout _ _) walking_span.left : _)

@[simp, reassoc]
lemma inr_pushout_left_pushout_inr_iso_hom :
  pushout.inr ≫ (pushout_left_pushout_inr_iso f g g').hom = pushout.inr :=
((big_square_is_pushout g g' _ _ f _ _ pushout.condition pushout.condition
  (pushout_is_pushout _ _) (pushout_is_pushout _ _))
  .comp_cocone_point_unique_up_to_iso_hom (pushout_is_pushout _ _) walking_span.right : _)

@[simp, reassoc]
lemma inr_pushout_left_pushout_inr_iso_inv :
  pushout.inr ≫ (pushout_left_pushout_inr_iso f g g').inv = pushout.inr :=
by rw [iso.comp_inv_eq, inr_pushout_left_pushout_inr_iso_hom]

@[simp, reassoc]
lemma inl_inl_pushout_left_pushout_inr_iso_hom :
  pushout.inl ≫ pushout.inl ≫ (pushout_left_pushout_inr_iso f g g').hom = pushout.inl :=
by rw [← category.assoc, ← iso.eq_comp_inv, inl_pushout_left_pushout_inr_iso_inv]

@[simp, reassoc]
lemma inr_inl_pushout_left_pushout_inr_iso_hom :
  pushout.inr ≫ pushout.inl ≫ (pushout_left_pushout_inr_iso f g g').hom = g' ≫ pushout.inr :=
by rw [← category.assoc, ← iso.eq_comp_inv, category.assoc,
  inr_pushout_left_pushout_inr_iso_inv, pushout.condition]

end

section pullback_assoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pullbacks.

We can then construct the pullback squares

W  - l₂ -> Z₂ - g₄ -> X₃
|                     |
l₁                    f₄
∨                     ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂

and

W' - l₂' -> Z₂
|           |
l₁'         g₃
∨           ∨
Z₁          X₂
|           |
g₁          f₂
∨           ∨
X₁ -  f₁ -> Y₁

We will show that both `W` and `W'` are pullbacks over `g₁, g₂`, and thus we may construct a
canonical isomorphism between them. -/

variables {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)
variables (f₄ : X₃ ⟶ Y₂) [has_pullback f₁ f₂] [has_pullback f₃ f₄]

include f₁ f₂ f₃ f₄

local notation `Z₁` := pullback f₁ f₂
local notation `Z₂` := pullback f₃ f₄
local notation `g₁` := (pullback.fst : Z₁ ⟶ X₁)
local notation `g₂` := (pullback.snd : Z₁ ⟶ X₂)
local notation `g₃` := (pullback.fst : Z₂ ⟶ X₂)
local notation `g₄` := (pullback.snd : Z₂ ⟶ X₃)
local notation `W`  := pullback (g₂ ≫ f₃) f₄
local notation `W'` := pullback f₁ (g₃ ≫ f₂)
local notation `l₁` := (pullback.fst : W ⟶ Z₁)
local notation `l₂` := (pullback.lift (pullback.fst ≫ g₂) pullback.snd
    ((category.assoc _ _ _).trans pullback.condition) : W ⟶ Z₂)
local notation `l₁'`:= (pullback.lift pullback.fst (pullback.snd ≫ g₃)
    (pullback.condition.trans (category.assoc _ _ _).symm) : W' ⟶ Z₁)
local notation `l₂'`:= (pullback.snd : W' ⟶ Z₂)

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullback_pullback_left_is_pullback [has_pullback (g₂ ≫ f₃) f₄] :
is_limit (pullback_cone.mk l₁ l₂ (show l₁ ≫ g₂ = l₂ ≫ g₃, from (pullback.lift_fst _ _ _).symm)) :=
begin
  apply left_square_is_pullback,
  exact pullback_is_pullback f₃ f₄,
  convert pullback_is_pullback (g₂ ≫ f₃) f₄,
  rw pullback.lift_snd
end

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
def pullback_assoc_is_pullback [has_pullback (g₂ ≫ f₃) f₄] :
is_limit (pullback_cone.mk (l₁ ≫ g₁) l₂ (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ (g₃ ≫ f₂),
  by rw [pullback.lift_fst_assoc, category.assoc, category.assoc, pullback.condition])) :=
begin
  apply pullback_cone.flip_is_limit,
  apply big_square_is_pullback,
  { apply pullback_cone.flip_is_limit,
    exact pullback_is_pullback f₁ f₂ },
  { apply pullback_cone.flip_is_limit,
    apply pullback_pullback_left_is_pullback },
  { exact pullback.lift_fst _ _ _ },
  { exact pullback.condition.symm }
end

lemma has_pullback_assoc [has_pullback (g₂ ≫ f₃) f₄] :
has_pullback f₁ (g₃ ≫ f₂) :=
⟨⟨⟨_, pullback_assoc_is_pullback f₁ f₂ f₃ f₄⟩⟩⟩

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullback_pullback_right_is_pullback [has_pullback f₁ (g₃ ≫ f₂)] :
is_limit (pullback_cone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃, from pullback.lift_snd _ _ _)) :=
begin
  apply pullback_cone.flip_is_limit,
  apply left_square_is_pullback,
  { apply pullback_cone.flip_is_limit,
    exact pullback_is_pullback f₁ f₂ },
  { apply pullback_cone.flip_is_limit,
    convert pullback_is_pullback f₁ (g₃ ≫ f₂),
    rw pullback.lift_fst },
  { exact pullback.condition.symm }
end

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
def pullback_assoc_symm_is_pullback [has_pullback f₁ (g₃ ≫ f₂)] :
is_limit (pullback_cone.mk l₁' (l₂' ≫ g₄) (show l₁' ≫ (g₂ ≫ f₃) = (l₂' ≫ g₄) ≫ f₄,
  by rw [pullback.lift_snd_assoc, category.assoc, category.assoc, pullback.condition])) :=
begin
  apply big_square_is_pullback,
  exact pullback_is_pullback f₃ f₄,
  apply pullback_pullback_right_is_pullback
end

lemma has_pullback_assoc_symm [has_pullback f₁ (g₃ ≫ f₂)] :
has_pullback (g₂ ≫ f₃) f₄ :=
⟨⟨⟨_, pullback_assoc_symm_is_pullback f₁ f₂ f₃ f₄⟩⟩⟩

variables [has_pullback (g₂ ≫ f₃) f₄] [has_pullback f₁ (g₃ ≫ f₂)]

/-- The canonical isomorphism `(X₁ ×[Y₁] X₂) ×[Y₂] X₃ ≅ X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
noncomputable
def pullback_assoc :
  pullback (pullback.snd ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
    pullback f₁ (pullback.fst ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
(pullback_pullback_left_is_pullback f₁ f₂ f₃ f₄).cone_point_unique_up_to_iso
(pullback_pullback_right_is_pullback f₁ f₂ f₃ f₄)

@[simp, reassoc]
lemma pullback_assoc_inv_fst_fst :
  (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.fst :=
begin
  transitivity l₁' ≫ pullback.fst,
  rw ← category.assoc,
  congr' 1,
  exact is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left,
  exact pullback.lift_fst _ _ _,
end

@[simp, reassoc]
lemma pullback_assoc_hom_fst :
  (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.fst = pullback.fst ≫ pullback.fst :=
by rw [← iso.eq_inv_comp, pullback_assoc_inv_fst_fst]

@[simp, reassoc]
lemma pullback_assoc_hom_snd_fst :
  (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
begin
  transitivity l₂ ≫ pullback.fst,
  rw ← category.assoc,
  congr' 1,
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right,
  exact pullback.lift_fst _ _ _,
end

@[simp, reassoc]
lemma pullback_assoc_hom_snd_snd :
  (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
begin
  transitivity l₂ ≫ pullback.snd,
  rw ← category.assoc,
  congr' 1,
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right,
  exact pullback.lift_snd _ _ _,
end

@[simp, reassoc]
lemma pullback_assoc_inv_fst_snd :
  (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.fst :=
by rw [iso.inv_comp_eq, pullback_assoc_hom_snd_fst]

@[simp, reassoc]
lemma pullback_assoc_inv_snd :
  (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by rw [iso.inv_comp_eq, pullback_assoc_hom_snd_snd]

end pullback_assoc


section pushout_assoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pushouts.

We can then construct the pushout squares

Z₁ - g₂ -> X₂ - f₃ -> Y₂
|                     |
g₁                    l₂
∨                     ∨
X₁ - f₁ -> Y₁ - l₁ -> W

and

Z₂ - g₄  -> X₃
|           |
g₃          f₄
∨           ∨
X₂          Y₂
|           |
f₂          l₂'
∨           ∨
Y₁ - l₁' -> W'

We will show that both `W` and `W'` are pushouts over `f₂, f₃`, and thus we may construct a
canonical isomorphism between them. -/

variables {X₁ X₂ X₃ Z₁ Z₂ : C} (g₁ : Z₁ ⟶ X₁) (g₂ : Z₁ ⟶ X₂) (g₃ : Z₂ ⟶ X₂)
variables (g₄ : Z₂ ⟶ X₃) [has_pushout g₁ g₂] [has_pushout g₃ g₄]

include g₁ g₂ g₃ g₄

local notation `Y₁` := pushout g₁ g₂
local notation `Y₂` := pushout g₃ g₄
local notation `f₁` := (pushout.inl : X₁ ⟶ Y₁)
local notation `f₂` := (pushout.inr : X₂ ⟶ Y₁)
local notation `f₃` := (pushout.inl : X₂ ⟶ Y₂)
local notation `f₄` := (pushout.inr : X₃ ⟶ Y₂)
local notation `W`  := pushout g₁ (g₂ ≫ f₃)
local notation `W'` := pushout (g₃ ≫ f₂) g₄
local notation `l₁` := (pushout.desc pushout.inl (f₃ ≫ pushout.inr)
  (pushout.condition.trans (category.assoc _ _ _)) : Y₁ ⟶ W)
local notation `l₂` := (pushout.inr : Y₂ ⟶ W)
local notation `l₁'`:= (pushout.inl : Y₁ ⟶ W')
local notation `l₂'`:= (pushout.desc (f₂ ≫ pushout.inl) pushout.inr
    ((category.assoc _ _ _).symm.trans pushout.condition) : Y₂ ⟶ W')

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushout_pushout_left_is_pushout [has_pushout (g₃ ≫ f₂) g₄] :
  is_colimit (pushout_cocone.mk l₁' l₂'
    (show f₂ ≫ l₁' = f₃ ≫ l₂', from (pushout.inl_desc _ _ _).symm)) :=
begin
  apply pushout_cocone.flip_is_colimit,
  apply right_square_is_pushout,
  { apply pushout_cocone.flip_is_colimit,
    exact pushout_is_pushout _ _ },
  { apply pushout_cocone.flip_is_colimit,
    convert pushout_is_pushout (g₃ ≫ f₂) g₄,
    exact pushout.inr_desc _ _ _ },
  { exact pushout.condition.symm }
end

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
def pushout_assoc_is_pushout [has_pushout (g₃ ≫ f₂) g₄] :
  is_colimit (pushout_cocone.mk (f₁ ≫ l₁') l₂' (show g₁ ≫ (f₁ ≫ l₁') = (g₂ ≫ f₃) ≫ l₂',
  by rw [category.assoc, pushout.inl_desc, pushout.condition_assoc])) :=
begin
  apply big_square_is_pushout,
  { apply pushout_pushout_left_is_pushout },
  { exact pushout_is_pushout _ _ }
end

lemma has_pushout_assoc [has_pushout (g₃ ≫ f₂) g₄] :
  has_pushout g₁ (g₂ ≫ f₃) :=
⟨⟨⟨_, pushout_assoc_is_pushout g₁ g₂ g₃ g₄⟩⟩⟩

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushout_pushout_right_is_pushout [has_pushout g₁ (g₂ ≫ f₃)] :
is_colimit (pushout_cocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂, from pushout.inr_desc _ _ _)) :=
begin
  apply right_square_is_pushout,
  { exact pushout_is_pushout _ _ },
  { convert pushout_is_pushout g₁ (g₂ ≫ f₃),
    rw pushout.inl_desc }
end

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃`. -/
def pushout_assoc_symm_is_pushout [has_pushout g₁ (g₂ ≫ f₃)] :
  is_colimit (pushout_cocone.mk l₁ (f₄ ≫ l₂) ((show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ (f₄ ≫ l₂),
    by rw [category.assoc, pushout.inr_desc, pushout.condition_assoc]))) :=
begin
  apply pushout_cocone.flip_is_colimit,
  apply big_square_is_pushout,
  { apply pushout_cocone.flip_is_colimit,
    apply pushout_pushout_right_is_pushout },
  { apply pushout_cocone.flip_is_colimit,
    exact pushout_is_pushout _ _ },
  { exact pushout.condition.symm },
  { exact (pushout.inr_desc _ _ _).symm }
end

lemma has_pushout_assoc_symm [has_pushout g₁ (g₂ ≫ f₃)] :
  has_pushout (g₃ ≫ f₂) g₄ :=
⟨⟨⟨_, pushout_assoc_symm_is_pushout g₁ g₂ g₃ g₄⟩⟩⟩

variables [has_pushout (g₃ ≫ f₂) g₄] [has_pushout g₁ (g₂ ≫ f₃)]


/-- The canonical isomorphism `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃ ≅ X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
noncomputable
def pushout_assoc :
  pushout (g₃ ≫ pushout.inr : _ ⟶ pushout g₁ g₂) g₄ ≅
    pushout g₁ (g₂ ≫ pushout.inl : _ ⟶ pushout g₃ g₄) :=
(pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).cocone_point_unique_up_to_iso
(pushout_pushout_right_is_pushout g₁ g₂ g₃ g₄)

@[simp, reassoc]
lemma inl_inl_pushout_assoc_hom :
  pushout.inl ≫ pushout.inl ≫ (pushout_assoc g₁ g₂ g₃ g₄).hom = pushout.inl :=
begin
  transitivity f₁ ≫ l₁,
  { congr' 1,
    exact (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄)
      .comp_cocone_point_unique_up_to_iso_hom _ walking_cospan.left },
  { exact pushout.inl_desc _ _ _ }
end

@[simp, reassoc]
lemma inr_inl_pushout_assoc_hom :
  pushout.inr ≫ pushout.inl ≫ (pushout_assoc g₁ g₂ g₃ g₄).hom = pushout.inl ≫ pushout.inr :=
begin
  transitivity f₂ ≫ l₁,
  { congr' 1,
    exact (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄)
      .comp_cocone_point_unique_up_to_iso_hom _ walking_cospan.left },
  { exact pushout.inr_desc _ _ _ }
end

@[simp, reassoc]
lemma inr_inr_pushout_assoc_inv :
  pushout.inr ≫ pushout.inr ≫ (pushout_assoc g₁ g₂ g₃ g₄).inv = pushout.inr :=
begin
  transitivity f₄ ≫ l₂',
  { congr' 1,
    exact (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).comp_cocone_point_unique_up_to_iso_inv
      (pushout_pushout_right_is_pushout g₁ g₂ g₃ g₄) walking_cospan.right },
  { exact pushout.inr_desc _ _ _ }
end

@[simp, reassoc]
lemma inl_pushout_assoc_inv :
  pushout.inl ≫ (pushout_assoc g₁ g₂ g₃ g₄).inv = pushout.inl ≫ pushout.inl :=
by rw [iso.comp_inv_eq, category.assoc, inl_inl_pushout_assoc_hom]

@[simp, reassoc]
lemma inl_inr_pushout_assoc_inv :
  pushout.inl ≫ pushout.inr ≫ (pushout_assoc g₁ g₂ g₃ g₄).inv = pushout.inr ≫ pushout.inl :=
by rw [← category.assoc, iso.comp_inv_eq, category.assoc, inr_inl_pushout_assoc_hom]

@[simp, reassoc]
lemma inr_pushout_assoc_hom :
  pushout.inr ≫  (pushout_assoc g₁ g₂ g₃ g₄).hom = pushout.inr ≫ pushout.inr :=
by rw [← iso.eq_comp_inv, category.assoc, inr_inr_pushout_assoc_inv]


end pushout_assoc

variables (C)

/--
`has_pullbacks` represents a choice of pullback for every pair of morphisms

See <https://stacks.math.columbia.edu/tag/001W>
-/
abbreviation has_pullbacks := has_limits_of_shape walking_cospan C

/-- `has_pushouts` represents a choice of pushout for every pair of morphisms -/
abbreviation has_pushouts := has_colimits_of_shape walking_span C

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
lemma has_pullbacks_of_has_limit_cospan
  [Π {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, has_limit (cospan f g)] :
  has_pullbacks C :=
{ has_limit := λ F, has_limit_of_iso (diagram_iso_cospan F).symm }

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
lemma has_pushouts_of_has_colimit_span
  [Π {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, has_colimit (span f g)] :
  has_pushouts C :=
{ has_colimit := λ F, has_colimit_of_iso (diagram_iso_span F) }

/-- The duality equivalence `walking_spanᵒᵖ ≌ walking_cospan` -/
@[simps]
def walking_span_op_equiv : walking_spanᵒᵖ ≌ walking_cospan :=
wide_pushout_shape_op_equiv _

/-- The duality equivalence `walking_cospanᵒᵖ ≌ walking_span` -/
@[simps]
def walking_cospan_op_equiv : walking_cospanᵒᵖ ≌ walking_span :=
wide_pullback_shape_op_equiv _

/-- Having wide pullback at any universe level implies having binary pullbacks. -/
@[priority 100] -- see Note [lower instance priority]
instance has_pullbacks_of_has_wide_pullbacks [has_wide_pullbacks.{w} C] : has_pullbacks C :=
begin
  haveI := has_wide_pullbacks_shrink.{0 w} C,
  apply_instance
end

variable {C}

/-- Given a morphism `f : X ⟶ Y`, we can take morphisms over `Y` to morphisms over `X` via
pullbacks. This is right adjoint to `over.map` (TODO) -/
@[simps obj_left obj_hom map_left {rhs_md := semireducible, simp_rhs := tt}]
def base_change [has_pullbacks C] {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj := λ g, over.mk (pullback.snd : pullback g.hom f ⟶ _),
  map := λ g₁ g₂ i, over.hom_mk (pullback.map _ _ _ _ i.left (𝟙 _) (𝟙 _) (by simp) (by simp))
    (by simp) }

end category_theory.limits
