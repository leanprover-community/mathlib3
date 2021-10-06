/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta
-/
import category_theory.limits.shapes.wide_pullbacks
import category_theory.limits.shapes.binary_products

/-!
# Pullbacks

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

universes v u u₂

local attribute [tidy] tactic.case_bash

/--
The type of objects for the diagram indexing a pullback, defined as a special case of
`wide_pullback_shape`.
-/
abbreviation walking_cospan : Type v := wide_pullback_shape walking_pair

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
abbreviation walking_span : Type v := wide_pushout_shape walking_pair

/-- The left point of the walking span. -/
@[pattern] abbreviation walking_span.left : walking_span := some walking_pair.left
/-- The right point of the walking span. -/
@[pattern] abbreviation walking_span.right : walking_span := some walking_pair.right
/-- The central point of the walking span. -/
@[pattern] abbreviation walking_span.zero : walking_span := none

namespace walking_cospan

/-- The type of arrows for the diagram indexing a pullback. -/
abbreviation hom : walking_cospan → walking_cospan → Type v := wide_pullback_shape.hom

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
abbreviation hom : walking_span → walking_span → Type v := wide_pushout_shape.hom

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

/-- Given `F : walking_span ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
    and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
def pushout_cocone.of_cocone
  {F : walking_span ⥤ C} (t : cocone F) : pushout_cocone (F.map fst) (F.map snd) :=
{ X := t.X,
  ι := (diagram_iso_span F).inv ≫ t.ι }

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

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext] lemma pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g]
  {W : C} {k l : pushout f g ⟶ W} (h₀ : pushout.inl ≫ k = pushout.inl ≫ l)
  (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
colimit.hom_ext $ pushout_cocone.coequalizer_ext _ h₀ h₁

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi g] :
  epi (pushout.inl : Y ⟶ pushout f g) :=
pushout_cocone.epi_inl_of_is_pushout_of_epi (colimit.is_colimit _)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi f] :
  epi (pushout.inr : Z ⟶ pushout f g) :=
pushout_cocone.epi_inr_of_is_pushout_of_epi (colimit.is_colimit _)

section

variables {D : Type u₂} [category.{v} D] (G : C ⥤ D)

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

end

variables (C)

/--
`has_pullbacks` represents a choice of pullback for every pair of morphisms

See https://stacks.math.columbia.edu/tag/001W.
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

end category_theory.limits
