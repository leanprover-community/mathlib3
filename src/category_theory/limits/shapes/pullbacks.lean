/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic
import category_theory.limits.limits
import category_theory.limits.shapes.finite_limits
import category_theory.sparse

/-!
# Pullbacks

We define a category `walking_cospan` (resp. `walking_span`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

Typeclasses `has_pullbacks` and `has_pushouts` assert the existence of (co)limits shaped as
walking (co)spans.
-/

open category_theory

namespace category_theory.limits

universes v u

local attribute [tidy] tactic.case_bash

/-- The type of objects for the diagram indexing a pullback. -/
@[derive decidable_eq] inductive walking_cospan : Type v
| left | right | one
/-- The type of objects for the diagram indexing a pushout. -/
@[derive decidable_eq] inductive walking_span : Type v
| zero | left | right

instance fintype_walking_cospan : fintype walking_cospan :=
{ elems := [walking_cospan.left, walking_cospan.right, walking_cospan.one].to_finset,
  complete := λ x, by { cases x; simp } }

instance fintype_walking_span : fintype walking_span :=
{ elems := [walking_span.zero, walking_span.left, walking_span.right].to_finset,
  complete := λ x, by { cases x; simp } }

namespace walking_cospan

/-- The arrows in a pullback diagram. -/
@[derive _root_.decidable_eq] inductive hom : walking_cospan → walking_cospan → Type v
| inl : hom left one
| inr : hom right one
| id : Π X : walking_cospan.{v}, hom X X

open hom

instance fintype_walking_cospan_hom (j j' : walking_cospan) : fintype (hom j j') :=
{ elems := walking_cospan.rec_on j
    (walking_cospan.rec_on j' [hom.id left].to_finset ∅ [inl].to_finset)
    (walking_cospan.rec_on j' ∅ [hom.id right].to_finset [inr].to_finset)
    (walking_cospan.rec_on j' ∅ ∅ [hom.id one].to_finset),
  complete := by tidy }

def hom.comp : Π (X Y Z : walking_cospan) (f : hom X Y) (g : hom Y Z), hom X Z
| _ _ _ (id _) h := h
| _ _ _ inl    (id one) := inl
| _ _ _ inr    (id one) := inr
.

instance category_struct : category_struct walking_cospan :=
{ hom  := hom,
  id   := hom.id,
  comp := hom.comp, }

instance (X Y : walking_cospan) : subsingleton (X ⟶ Y) := by tidy

-- We make this a @[simp] lemma later; if we do it now there's a mysterious
-- failure in `cospan`, below.
lemma hom_id (X : walking_cospan.{v}) : hom.id X = 𝟙 X := rfl

/-- The walking_cospan is the index diagram for a pullback. -/
instance : small_category.{v} walking_cospan.{v} := sparse_category

instance : fin_category.{v} walking_cospan.{v} :=
{ fintype_hom := walking_cospan.fintype_walking_cospan_hom }

end walking_cospan

namespace walking_span

/-- The arrows in a pushout diagram. -/
@[derive _root_.decidable_eq] inductive hom : walking_span → walking_span → Type v
| fst : hom zero left
| snd : hom zero right
| id : Π X : walking_span.{v}, hom X X

open hom

instance fintype_walking_span_hom (j j' : walking_span) : fintype (hom j j') :=
{ elems := walking_span.rec_on j
    (walking_span.rec_on j' [hom.id zero].to_finset [fst].to_finset [snd].to_finset)
    (walking_span.rec_on j' ∅ [hom.id left].to_finset ∅)
    (walking_span.rec_on j' ∅ ∅ [hom.id right].to_finset),
  complete := by tidy }

def hom.comp : Π (X Y Z : walking_span) (f : hom X Y) (g : hom Y Z), hom X Z
  | _ _ _ (id _) h := h
  | _ _ _ fst    (id left) := fst
  | _ _ _ snd    (id right) := snd
.

instance category_struct : category_struct walking_span :=
{ hom  := hom,
  id   := hom.id,
  comp := hom.comp }

instance (X Y : walking_span) : subsingleton (X ⟶ Y) := by tidy

-- We make this a @[simp] lemma later; if we do it now there's a mysterious
-- failure in `span`, below.
lemma hom_id (X : walking_span.{v}) : hom.id X = 𝟙 X := rfl

/-- The walking_span is the index diagram for a pushout. -/
instance : small_category.{v} walking_span.{v} := sparse_category

instance : fin_category.{v} walking_span.{v} :=
{ fintype_hom := walking_span.fintype_walking_span_hom }

end walking_span

open walking_span walking_cospan walking_span.hom walking_cospan.hom

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan.{v} ⥤ C :=
{ obj := λ x, match x with
  | left := X
  | right := Y
  | one := Z
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, inl := f
  | _, _, inr := g
  end }

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : walking_span.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | left := Y
  | right := Z
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, fst := f
  | _, _, snd := g
  end }

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

/-- Every diagram indexing an equalizer is naturally isomorphic (actually, equal) to a `cospan` -/
def diagram_iso_cospan (F : walking_cospan ⥤ C) :
  F ≅ cospan (F.map inl) (F.map inr) :=
nat_iso.of_components (λ j, eq_to_iso $ by cases j; tidy) $ by tidy

/-- Every diagram indexing a coequalizer naturally isomorphic (actually, equal) to a `span` -/
def diagram_iso_span (F : walking_span ⥤ C) :
  F ≅ span (F.map fst) (F.map snd) :=
nat_iso.of_components (λ j, eq_to_iso $ by cases j; tidy) $ by tidy

variables {X Y Z : C}

attribute [simp] walking_cospan.hom_id walking_span.hom_id

abbreviation pullback_cone (f : X ⟶ Z) (g : Y ⟶ Z) := cone (cospan f g)

namespace pullback_cone
variables {f : X ⟶ Z} {g : Y ⟶ Z}

abbreviation fst (t : pullback_cone f g) : t.X ⟶ X := t.π.app left
abbreviation snd (t : pullback_cone f g) : t.X ⟶ Y := t.π.app right

def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : pullback_cone f g :=
{ X := W,
  π :=
  { app := λ j, walking_cospan.cases_on j fst snd (fst ≫ f),
    naturality' := λ j j' f, by cases f; obviously } }

@[simp] lemma mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).π.app left = fst := rfl
@[simp] lemma mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).π.app right = snd := rfl
@[simp] lemma mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (mk fst snd eq).π.app one = fst ≫ f := rfl

@[reassoc] lemma condition (t : pullback_cone f g) : fst t ≫ f = snd t ≫ g :=
begin
  erw [t.w inl, ← t.w inr], refl
end

/-- To check whether a morphism is equalized by the maps of a pullback cone, it suffices to check
  it for `fst t` and `snd t` -/
lemma equalizer_ext (t : pullback_cone f g) {W : C} {k l : W ⟶ t.X}
  (h₀ : k ≫ fst t = l ≫ fst t)
  (h₁ : k ≫ snd t = l ≫ snd t) :
  ∀ (j : walking_cospan), k ≫ t.π.app j = l ≫ t.π.app j
| left := h₀
| right := h₁
| one := calc k ≫ t.π.app one = k ≫ t.π.app left ≫ (cospan f g).map inl : by rw ←t.w
    ... = l ≫ t.π.app left ≫ (cospan f g).map inl : by rw [←category.assoc, h₀, category.assoc]
    ... = l ≫ t.π.app one : by rw t.w

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit.mk (t : pullback_cone f g) (lift : Π (s : cone (cospan f g)), s.X ⟶ t.X)
  (fac_left : ∀ (s : cone (cospan f g)), lift s ≫ t.π.app left = s.π.app left)
  (fac_right : ∀ (s : cone (cospan f g)), lift s ≫ t.π.app right = s.π.app right)
  (uniq : ∀ (s : cone (cospan f g)) (m : s.X ⟶ t.X)
    (w : ∀ j : walking_cospan, m ≫ t.π.app j = s.π.app j), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j, walking_cospan.cases_on j (fac_left s) (fac_right s) $
    by rw [←t.w inl, ←s.w inl, ←fac_left s, category.assoc],
  uniq' := uniq }

end pullback_cone

abbreviation pushout_cocone (f : X ⟶ Y) (g : X ⟶ Z) := cocone (span f g)

namespace pushout_cocone

variables {f : X ⟶ Y} {g : X ⟶ Z}

abbreviation inl (t : pushout_cocone f g) : Y ⟶ t.X := t.ι.app left
abbreviation inr (t : pushout_cocone f g) : Z ⟶ t.X := t.ι.app right

def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : pushout_cocone f g :=
{ X := W,
  ι :=
  { app := λ j, walking_span.cases_on j (f ≫ inl) inl inr,
    naturality' := λ j j' f, by cases f; obviously } }

@[simp] lemma mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).ι.app left = inl := rfl
@[simp] lemma mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).ι.app right = inr := rfl
@[simp] lemma mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
  (mk inl inr eq).ι.app zero = f ≫ inl := rfl

@[reassoc] lemma condition (t : pushout_cocone f g) : f ≫ (inl t) = g ≫ (inr t) :=
begin
  erw [t.w fst, ← t.w snd], refl
end

/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
lemma coequalizer_ext (t : pushout_cocone f g) {W : C} {k l : t.X ⟶ W}
  (h₀ : inl t ≫ k = inl t ≫ l)
  (h₁ : inr t ≫ k = inr t ≫ l) :
  ∀ (j : walking_span), t.ι.app j ≫ k = t.ι.app j ≫ l
| left := h₀
| right := h₁
| zero := calc t.ι.app zero ≫ k = ((span f g).map fst ≫ t.ι.app left) ≫ k : by rw ←t.w
    ... = ((span f g).map fst ≫ t.ι.app left) ≫ l : by rw [category.assoc, h₀, ←category.assoc]
    ... = t.ι.app zero ≫ l : by rw t.w

/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
    It only asks for a proof of facts that carry any mathematical content -/
def is_colimit.mk (t : pushout_cocone f g) (desc : Π (s : cocone (span f g)), t.X ⟶ s.X)
  (fac_left : ∀ (s : cocone (span f g)), t.ι.app left ≫ desc s = s.ι.app left)
  (fac_right : ∀ (s : cocone (span f g)), t.ι.app right ≫ desc s = s.ι.app right)
  (uniq : ∀ (s : cocone (span f g)) (m : t.X ⟶ s.X)
    (w : ∀ j : walking_span, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
  is_colimit t :=
{ desc := desc,
  fac' := λ s j, walking_span.cases_on j (by rw [←s.w fst, ←t.w fst, category.assoc, fac_left s])
    (fac_left s) (fac_right s),
  uniq' := uniq }

end pushout_cocone

def cone.of_pullback_cone
  {F : walking_cospan.{v} ⥤ C} (t : pullback_cone (F.map inl) (F.map inr)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      exact (t.w inl).symm,
      exact (t.w inr).symm
    end } }.

@[simp] lemma cone.of_pullback_cone_π
  {F : walking_cospan.{v} ⥤ C} (t : pullback_cone (F.map inl) (F.map inr)) (j) :
  (cone.of_pullback_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

def cocone.of_pushout_cocone
  {F : walking_span.{v} ⥤ C} (t : pushout_cocone (F.map fst) (F.map snd)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      exact t.w fst,
      exact t.w snd
    end } }.

@[simp] lemma cocone.of_pushout_cocone_ι
  {F : walking_span.{v} ⥤ C} (t : pushout_cocone (F.map fst) (F.map snd)) (j) :
  (cocone.of_pushout_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

def pullback_cone.of_cone
  {F : walking_cospan.{v} ⥤ C} (t : cone F) : pullback_cone (F.map inl) (F.map inr) :=
{ X := t.X,
  π := { app := λ j, t.π.app j ≫ eq_to_hom (by tidy) } }

@[simp] lemma pullback_cone.of_cone_π {F : walking_cospan.{v} ⥤ C} (t : cone F) (j) :
  (pullback_cone.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

def pushout_cocone.of_cocone
  {F : walking_span.{v} ⥤ C} (t : cocone F) : pushout_cocone (F.map fst) (F.map snd) :=
{ X := t.X,
  ι := { app := λ j, eq_to_hom (by tidy) ≫ t.ι.app j } }

@[simp] lemma pushout_cocone.of_cocone_ι {F : walking_span.{v} ⥤ C} (t : cocone F) (j) :
  (pushout_cocone.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbreviation pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] :=
limit (cospan f g)
/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbreviation pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (span f g)] :=
colimit (span f g)

abbreviation pullback.fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)] : pullback f g ⟶ X :=
limit.π (cospan f g) walking_cospan.left
abbreviation pullback.snd {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)] : pullback f g ⟶ Y :=
limit.π (cospan f g) walking_cospan.right
abbreviation pushout.inl {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_colimit (span f g)] : Y ⟶ pushout f g :=
colimit.ι (span f g) walking_span.left
abbreviation pushout.inr {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_colimit (span f g)] : Z ⟶ pushout f g :=
colimit.ι (span f g) walking_span.right

abbreviation pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
  (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
limit.lift _ (pullback_cone.mk h k w)
abbreviation pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_colimit (span f g)]
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
colimit.desc _ (pushout_cocone.mk h k w)

lemma pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)] :
  (pullback.fst : pullback f g ⟶ X) ≫ f = pullback.snd ≫ g :=
(limit.w (cospan f g) walking_cospan.hom.inl).trans
(limit.w (cospan f g) walking_cospan.hom.inr).symm

lemma pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_colimit (span f g)] :
  f ≫ (pushout.inl : Y ⟶ pushout f g) = g ≫ pushout.inr :=
(colimit.w (span f g) walking_span.hom.fst).trans
(colimit.w (span f g) walking_span.hom.snd).symm

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
@[ext] lemma pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
  {W : C} {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst = l ≫ pullback.fst)
  (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
limit.hom_ext $ pullback_cone.equalizer_ext _ h₀ h₁

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
  [mono g] : mono (pullback.fst : pullback f g ⟶ X) :=
⟨λ W u v h, pullback.hom_ext h $ (cancel_mono g).1 $
  calc (u ≫ pullback.snd) ≫ g = u ≫ pullback.fst ≫ f : by rw [category.assoc, pullback.condition]
    ... = v ≫ pullback.fst ≫ f : by rw [←category.assoc, h, category.assoc]
    ... = (v ≫ pullback.snd) ≫ g : by rw [pullback.condition, ←category.assoc]⟩

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
  [mono f] : mono (pullback.snd : pullback f g ⟶ Y) :=
⟨λ W u v h, pullback.hom_ext ((cancel_mono f).1 $
  calc (u ≫ pullback.fst) ≫ f = u ≫ pullback.snd ≫ g : by rw [category.assoc, pullback.condition]
    ... = v ≫ pullback.snd ≫ g : by rw [←category.assoc, h, category.assoc]
    ... = (v ≫ pullback.fst) ≫ f : by rw [←pullback.condition, ←category.assoc]) h⟩

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext] lemma pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_colimit (span f g)]
  {W : C} {k l : pushout f g ⟶ W} (h₀ : pushout.inl ≫ k = pushout.inl ≫ l)
  (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
colimit.hom_ext $ pushout_cocone.coequalizer_ext _ h₀ h₁

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_colimit (span f g)] [epi g] :
  epi (pushout.inl : Y ⟶ pushout f g) :=
⟨λ W u v h, pushout.hom_ext h $ (cancel_epi g).1 $
  calc g ≫ pushout.inr ≫ u = (f ≫ pushout.inl) ≫ u : by rw [←category.assoc, ←pushout.condition]
    ... = f ≫ pushout.inl ≫ v : by rw [category.assoc, h]
    ... = g ≫ pushout.inr ≫ v : by rw [←category.assoc, pushout.condition, category.assoc]⟩

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_colimit (span f g)] [epi f] :
  epi (pushout.inr : Z ⟶ pushout f g) :=
⟨λ W u v h, pushout.hom_ext ((cancel_epi f).1 $
  calc f ≫ pushout.inl ≫ u = (g ≫ pushout.inr) ≫ u : by rw [←category.assoc, pushout.condition]
    ... = g ≫ pushout.inr ≫ v : by rw [category.assoc, h]
    ... = f ≫ pushout.inl ≫ v : by rw [←category.assoc, ←pushout.condition, category.assoc]) h⟩

variables (C)

/-- `has_pullbacks` represents a choice of pullback for every pair of morphisms -/
class has_pullbacks :=
(has_limits_of_shape : has_limits_of_shape.{v} walking_cospan C)

/-- `has_pushouts` represents a choice of pushout for every pair of morphisms -/
class has_pushouts :=
(has_colimits_of_shape : has_colimits_of_shape.{v} walking_span C)

attribute [instance] has_pullbacks.has_limits_of_shape has_pushouts.has_colimits_of_shape

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
def has_pullbacks_of_has_finite_limits [has_finite_limits.{v} C] : has_pullbacks.{v} C :=
{ has_limits_of_shape := infer_instance }

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
def has_pushouts_of_has_finite_colimits [has_finite_colimits.{v} C] : has_pushouts.{v} C :=
{ has_colimits_of_shape := infer_instance }

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
def has_pullbacks_of_has_limit_cospan
  [Π {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, has_limit (cospan f g)] :
  has_pullbacks.{v} C :=
{ has_limits_of_shape := { has_limit := λ F, has_limit_of_iso (diagram_iso_cospan F).symm } }

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
def has_pushouts_of_has_colimit_span
  [Π {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, has_colimit (span f g)] :
  has_pushouts.{v} C :=
{ has_colimits_of_shape := { has_colimit := λ F, has_colimit_of_iso (diagram_iso_span F) } }

end category_theory.limits
