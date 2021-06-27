/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.epi_mono
import category_theory.limits.has_limits

/-!
# Equalizers and coequalizers

This file defines (co)equalizers as special cases of (co)limits.

An equalizer is the categorical generalization of the subobject {a ∈ A | f(a) = g(a)} known
from abelian groups or modules. It is a limit cone over the diagram formed by `f` and `g`.

A coequalizer is the dual concept.

## Main definitions

* `walking_parallel_pair` is the indexing category used for (co)equalizer_diagrams
* `parallel_pair` is a functor from `walking_parallel_pair` to our category `C`.
* a `fork` is a cone over a parallel pair.
  * there is really only one interesting morphism in a fork: the arrow from the vertex of the fork
    to the domain of f and g. It is called `fork.ι`.
* an `equalizer` is now just a `limit (parallel_pair f g)`

Each of these has a dual.

## Main statements

* `equalizer.ι_mono` states that every equalizer map is a monomorphism
* `is_iso_limit_cone_parallel_pair_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

noncomputable theory

open category_theory

namespace category_theory.limits

local attribute [tidy] tactic.case_bash

universes v u u₂

/-- The type of objects for the diagram indexing a (co)equalizer. -/
@[derive decidable_eq, derive inhabited] inductive walking_parallel_pair : Type v
| zero | one

open walking_parallel_pair

/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
@[derive decidable_eq] inductive walking_parallel_pair_hom :
  walking_parallel_pair → walking_parallel_pair → Type v
| left : walking_parallel_pair_hom zero one
| right : walking_parallel_pair_hom zero one
| id : Π X : walking_parallel_pair.{v}, walking_parallel_pair_hom X X

/-- Satisfying the inhabited linter -/
instance : inhabited (walking_parallel_pair_hom zero one) :=
{ default := walking_parallel_pair_hom.left }

open walking_parallel_pair_hom

/-- Composition of morphisms in the indexing diagram for (co)equalizers. -/
def walking_parallel_pair_hom.comp :
  Π (X Y Z : walking_parallel_pair)
    (f : walking_parallel_pair_hom X Y) (g : walking_parallel_pair_hom Y Z),
    walking_parallel_pair_hom X Z
  | _ _ _ (id _) h := h
  | _ _ _ left   (id one) := left
  | _ _ _ right  (id one) := right
.

instance walking_parallel_pair_hom_category : small_category walking_parallel_pair :=
{ hom  := walking_parallel_pair_hom,
  id   := walking_parallel_pair_hom.id,
  comp := walking_parallel_pair_hom.comp }

@[simp]
lemma walking_parallel_pair_hom_id (X : walking_parallel_pair) :
  walking_parallel_pair_hom.id X = 𝟙 X :=
rfl

variables {C : Type u} [category.{v} C]
variables {X Y : C}

/-- `parallel_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
    common domain and codomain. -/
def parallel_pair (f g : X ⟶ Y) : walking_parallel_pair.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | one := Y
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, left := f
  | _, _, right := g
  end,
  -- `tidy` can cope with this, but it's too slow:
  map_comp' := begin rintros (⟨⟩|⟨⟩) (⟨⟩|⟨⟩) (⟨⟩|⟨⟩) ⟨⟩⟨⟩; { unfold_aux, simp; refl }, end, }.

@[simp] lemma parallel_pair_obj_zero (f g : X ⟶ Y) : (parallel_pair f g).obj zero = X := rfl
@[simp] lemma parallel_pair_obj_one (f g : X ⟶ Y) : (parallel_pair f g).obj one = Y := rfl

@[simp] lemma parallel_pair_map_left (f g : X ⟶ Y) : (parallel_pair f g).map left = f := rfl
@[simp] lemma parallel_pair_map_right (f g : X ⟶ Y) : (parallel_pair f g).map right = g := rfl

@[simp] lemma parallel_pair_functor_obj
  {F : walking_parallel_pair ⥤ C} (j : walking_parallel_pair) :
  (parallel_pair (F.map left) (F.map right)).obj j = F.obj j :=
begin
  cases j; refl
end

/-- Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallel_pair` -/
@[simps]
def diagram_iso_parallel_pair (F : walking_parallel_pair ⥤ C) :
  F ≅ parallel_pair (F.map left) (F.map right) :=
nat_iso.of_components (λ j, eq_to_iso $ by cases j; tidy) $ by tidy

/-- Construct a morphism between parallel pairs. -/
def parallel_pair_hom {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
  (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : parallel_pair f g ⟶ parallel_pair f' g' :=
{ app := λ j, match j with
  | zero := p
  | one := q
  end,
  naturality' := begin
    rintros (⟨⟩|⟨⟩) (⟨⟩|⟨⟩) ⟨⟩; { unfold_aux, simp [wf, wg], },
  end }

@[simp] lemma parallel_pair_hom_app_zero
  {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
  (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
  (parallel_pair_hom f g f' g' p q wf wg).app zero = p := rfl

@[simp] lemma parallel_pair_hom_app_one
  {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
  (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
  (parallel_pair_hom f g f' g' p q wf wg).app one = q := rfl

/-- A fork on `f` and `g` is just a `cone (parallel_pair f g)`. -/
abbreviation fork (f g : X ⟶ Y) := cone (parallel_pair f g)

/-- A cofork on `f` and `g` is just a `cocone (parallel_pair f g)`. -/
abbreviation cofork (f g : X ⟶ Y) := cocone (parallel_pair f g)

variables {f g : X ⟶ Y}

/-- A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms `t.π.app zero : t.X ⟶ X`
    and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is interesting, and we give it the
    shorter name `fork.ι t`. -/
abbreviation fork.ι (t : fork f g) := t.π.app zero

/-- A cofork `t` on the parallel_pair `f g : X ⟶ Y` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `cofork.π t`. -/
abbreviation cofork.π (t : cofork f g) := t.ι.app one

@[simp] lemma fork.ι_eq_app_zero (t : fork f g) : t.ι = t.π.app zero := rfl
@[simp] lemma cofork.π_eq_app_one (t : cofork f g) : t.π = t.ι.app one := rfl

@[simp, reassoc] lemma fork.app_zero_left (s : fork f g) :
  s.π.app zero ≫ f = s.π.app one :=
by rw [←s.w left, parallel_pair_map_left]

@[simp, reassoc] lemma fork.app_zero_right (s : fork f g) :
  s.π.app zero ≫ g = s.π.app one :=
by rw [←s.w right, parallel_pair_map_right]

@[simp, reassoc] lemma cofork.left_app_one (s : cofork f g) :
  f ≫ s.ι.app one = s.ι.app zero :=
by rw [←s.w left, parallel_pair_map_left]

@[simp, reassoc] lemma cofork.right_app_one (s : cofork f g) :
  g ≫ s.ι.app one = s.ι.app zero :=
by rw [←s.w right, parallel_pair_map_right]

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
@[simps]
def fork.of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork f g :=
{ X := P,
  π :=
  { app := λ X, begin cases X, exact ι, exact ι ≫ f, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      { dsimp, simp, }, -- See note [dsimp, simp].
      { exact w },
      { dsimp, simp, },
    end } }

/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
    `f ≫ π = g ≫ π`. -/
@[simps]
def cofork.of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : cofork f g :=
{ X := P,
  ι :=
  { app := λ X, walking_parallel_pair.cases_on X (f ≫ π) π,
    naturality' := λ i j f, by { cases f; dsimp; simp [w] } } } -- See note [dsimp, simp]

lemma fork.ι_of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).ι = ι := rfl
lemma cofork.π_of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  (cofork.of_π π w).π = π := rfl

@[reassoc]
lemma fork.condition (t : fork f g) : t.ι ≫ f = t.ι ≫ g :=
by rw [t.app_zero_left, t.app_zero_right]
@[reassoc]
lemma cofork.condition (t : cofork f g) : f ≫ t.π = g ≫ t.π :=
by rw [t.left_app_one, t.right_app_one]

/-- To check whether two maps are equalized by both maps of a fork, it suffices to check it for the
    first map -/
lemma fork.equalizer_ext (s : fork f g) {W : C} {k l : W ⟶ s.X}
  (h : k ≫ fork.ι s = l ≫ fork.ι s) : ∀ (j : walking_parallel_pair),
    k ≫ s.π.app j = l ≫ s.π.app j
| zero := h
| one := by rw [←fork.app_zero_left, reassoc_of h]

/-- To check whether two maps are coequalized by both maps of a cofork, it suffices to check it for
    the second map -/
lemma cofork.coequalizer_ext (s : cofork f g) {W : C} {k l : s.X ⟶ W}
  (h : cofork.π s ≫ k = cofork.π s ≫ l) : ∀ (j : walking_parallel_pair),
    s.ι.app j ≫ k = s.ι.app j ≫ l
| zero := by simp only [←cofork.left_app_one, category.assoc, h]
| one := h

lemma fork.is_limit.hom_ext {s : fork f g} (hs : is_limit s) {W : C} {k l : W ⟶ s.X}
  (h : k ≫ fork.ι s = l ≫ fork.ι s) : k = l :=
hs.hom_ext $ fork.equalizer_ext _ h

lemma cofork.is_colimit.hom_ext {s : cofork f g} (hs : is_colimit s) {W : C} {k l : s.X ⟶ W}
  (h : cofork.π s ≫ k = cofork.π s ≫ l) : k = l :=
hs.hom_ext $ cofork.coequalizer_ext _ h

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
    `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
def fork.is_limit.lift' {s : fork f g} (hs : is_limit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
  {l : W ⟶ s.X // l ≫ fork.ι s = k} :=
⟨hs.lift $ fork.of_ι _ h, hs.fac _ _⟩

/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
    `f ≫ k = g ≫ k` induces a morphism `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def cofork.is_colimit.desc' {s : cofork f g} (hs : is_colimit s) {W : C} (k : Y ⟶ W)
  (h : f ≫ k = g ≫ k) : {l : s.X ⟶ W // cofork.π s ≫ l = k} :=
⟨hs.desc $ cofork.of_π _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def fork.is_limit.mk (t : fork f g)
  (lift : Π (s : fork f g), s.X ⟶ t.X)
  (fac : ∀ (s : fork f g), lift s ≫ fork.ι t = fork.ι s)
  (uniq : ∀ (s : fork f g) (m : s.X ⟶ t.X)
    (w : ∀ j : walking_parallel_pair, m ≫ t.π.app j = s.π.app j), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j, walking_parallel_pair.cases_on j (fac s) $
    by erw [←s.w left, ←t.w left, ←category.assoc, fac]; refl,
  uniq' := uniq }

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def fork.is_limit.mk' {X Y : C} {f g : X ⟶ Y} (t : fork f g)
  (create : Π (s : fork f g), {l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l}) :
is_limit t :=
fork.is_limit.mk t
  (λ s, (create s).1)
  (λ s, (create s).2.1)
  (λ s m w, (create s).2.2 (w zero))

/-- This is a slightly more convenient method to verify that a cofork is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
def cofork.is_colimit.mk (t : cofork f g)
  (desc : Π (s : cofork f g), t.X ⟶ s.X)
  (fac : ∀ (s : cofork f g), cofork.π t ≫ desc s = cofork.π s)
  (uniq : ∀ (s : cofork f g) (m : t.X ⟶ s.X)
    (w : ∀ j : walking_parallel_pair, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
  is_colimit t :=
{ desc := desc,
  fac' := λ s j, walking_parallel_pair.cases_on j
    (by erw [←s.w left, ←t.w left, category.assoc, fac]; refl) (fac s),
  uniq' := uniq }

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def cofork.is_colimit.mk' {X Y : C} {f g : X ⟶ Y} (t : cofork f g)
  (create : Π (s : cofork f g), {l : t.X ⟶ s.X // t.π ≫ l = s.π ∧ ∀ {m}, t.π ≫ m = s.π → m = l}) :
is_colimit t :=
cofork.is_colimit.mk t
  (λ s, (create s).1)
  (λ s, (create s).2.1)
  (λ s m w, (create s).2.2 (w one))

/--
Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` to its point are in
bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `fork.is_limit.hom_iso_natural`.
This is a special case of `is_limit.hom_iso'`, often useful to construct adjunctions.
-/
@[simps]
def fork.is_limit.hom_iso {X Y : C} {f g : X ⟶ Y} {t : fork f g} (ht : is_limit t) (Z : C) :
  (Z ⟶ t.X) ≃ {h : Z ⟶ X // h ≫ f = h ≫ g} :=
{ to_fun := λ k, ⟨k ≫ t.ι, by simp⟩,
  inv_fun := λ h, (fork.is_limit.lift' ht _ h.prop).1,
  left_inv := λ k, fork.is_limit.hom_ext ht (fork.is_limit.lift' _ _ _).prop,
  right_inv := λ h, subtype.ext (fork.is_limit.lift' ht _ _).prop }

/-- The bijection of `fork.is_limit.hom_iso` is natural in `Z`. -/
lemma fork.is_limit.hom_iso_natural {X Y : C} {f g : X ⟶ Y} {t : fork f g} (ht : is_limit t)
  {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.X) :
  (fork.is_limit.hom_iso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (fork.is_limit.hom_iso ht _ k : Z ⟶ X) :=
category.assoc _ _ _

/--
Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from the cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `cofork.is_colimit.hom_iso_natural`.
This is a special case of `is_colimit.hom_iso'`, often useful to construct adjunctions.
-/
@[simps]
def cofork.is_colimit.hom_iso {X Y : C} {f g : X ⟶ Y} {t : cofork f g} (ht : is_colimit t) (Z : C) :
  (t.X ⟶ Z) ≃ {h : Y ⟶ Z // f ≫ h = g ≫ h} :=
{ to_fun := λ k, ⟨t.π ≫ k, by simp⟩,
  inv_fun := λ h, (cofork.is_colimit.desc' ht _ h.prop).1,
  left_inv := λ k, cofork.is_colimit.hom_ext ht (cofork.is_colimit.desc' _ _ _).prop,
  right_inv := λ h, subtype.ext (cofork.is_colimit.desc' ht _ _).prop }

/-- The bijection of `cofork.is_colimit.hom_iso` is natural in `Z`. -/
lemma cofork.is_colimit.hom_iso_natural {X Y : C} {f g : X ⟶ Y} {t : cofork f g} {Z Z' : C}
  (q : Z ⟶ Z') (ht : is_colimit t) (k : t.X ⟶ Z) :
    (cofork.is_colimit.hom_iso ht _ (k ≫ q) : Y ⟶ Z') =
    (cofork.is_colimit.hom_iso ht _ k : Y ⟶ Z) ≫ q :=
(category.assoc _ _ _).symm

/-- This is a helper construction that can be useful when verifying that a category has all
    equalizers. Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)`, and a fork on `F.map left` and `F.map right`,
    we get a cone on `F`.

    If you're thinking about using this, have a look at `has_equalizers_of_has_limit_parallel_pair`,
    which you may find to be an easier way of achieving your goal. -/
def cone.of_fork
  {F : walking_parallel_pair ⥤ C} (t : fork (F.map left) (F.map right)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g, by { cases j; cases j'; cases g; dsimp; simp } } }

/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)`, and a cofork on `F.map left` and `F.map right`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at
    `has_coequalizers_of_has_colimit_parallel_pair`, which you may find to be an easier way of
    achieving your goal. -/
def cocone.of_cofork
  {F : walking_parallel_pair ⥤ C} (t : cofork (F.map left) (F.map right)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g, by { cases j; cases j'; cases g; dsimp; simp } } }

@[simp] lemma cone.of_fork_π
  {F : walking_parallel_pair ⥤ C} (t : fork (F.map left) (F.map right)) (j) :
  (cone.of_fork t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

@[simp] lemma cocone.of_cofork_ι
  {F : walking_parallel_pair ⥤ C} (t : cofork (F.map left) (F.map right)) (j) :
  (cocone.of_cofork t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

/-- Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)` and a cone on `F`, we get a fork on
    `F.map left` and `F.map right`. -/
def fork.of_cone
  {F : walking_parallel_pair ⥤ C} (t : cone F) : fork (F.map left) (F.map right) :=
{ X := t.X,
  π := { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }

/-- Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)` and a cocone on `F`, we get a cofork on
    `F.map left` and `F.map right`. -/
def cofork.of_cocone
  {F : walking_parallel_pair ⥤ C} (t : cocone F) : cofork (F.map left) (F.map right) :=
{ X := t.X,
  ι := { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X } }

@[simp] lemma fork.of_cone_π {F : walking_parallel_pair ⥤ C} (t : cone F) (j) :
  (fork.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl
@[simp] lemma cofork.of_cocone_ι {F : walking_parallel_pair ⥤ C} (t : cocone F) (j) :
  (cofork.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

/--
Helper function for constructing morphisms between equalizer forks.
-/
@[simps]
def fork.mk_hom {s t : fork f g} (k : s.X ⟶ t.X) (w : k ≫ t.ι = s.ι) : s ⟶ t :=
{ hom := k,
  w' :=
  begin
    rintro ⟨_|_⟩,
    { exact w },
    { simpa using w =≫ f },
  end }

/--
To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
def fork.ext {s t : fork f g} (i : s.X ≅ t.X) (w : i.hom ≫ t.ι = s.ι) : s ≅ t :=
{ hom := fork.mk_hom i.hom w,
  inv := fork.mk_hom i.inv (by rw [← w, iso.inv_hom_id_assoc]) }

/--
Helper function for constructing morphisms between coequalizer coforks.
-/
@[simps]
def cofork.mk_hom {s t : cofork f g} (k : s.X ⟶ t.X) (w : s.π ≫ k = t.π) : s ⟶ t :=
{ hom := k,
  w' :=
  begin
    rintro ⟨_|_⟩,
    simpa using f ≫= w,
    exact w,
  end }

/--
To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def cofork.ext {s t : cofork f g} (i : s.X ≅ t.X) (w : s.π ≫ i.hom = t.π) : s ≅ t :=
{ hom := cofork.mk_hom i.hom w,
  inv := cofork.mk_hom i.inv (by rw [iso.comp_inv_eq, w]) }

variables (f g)

section
/--
`has_equalizer f g` represents a particular choice of limiting cone
for the parallel pair of morphisms `f` and `g`.
-/
abbreviation has_equalizer := has_limit (parallel_pair f g)

variables [has_equalizer f g]

/-- If an equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `equalizer f g`. -/
abbreviation equalizer : C := limit (parallel_pair f g)

/-- If an equalizer of `f` and `g` exists, we can access the inclusion
    `equalizer f g ⟶ X` by saying `equalizer.ι f g`. -/
abbreviation equalizer.ι : equalizer f g ⟶ X :=
limit.π (parallel_pair f g) zero

/--
An equalizer cone for a parallel pair `f` and `g`.
-/
abbreviation equalizer.fork : fork f g := limit.cone (parallel_pair f g)

@[simp] lemma equalizer.fork_ι :
  (equalizer.fork f g).ι = equalizer.ι f g := rfl

@[simp] lemma equalizer.fork_π_app_zero :
  (equalizer.fork f g).π.app zero = equalizer.ι f g := rfl

@[reassoc] lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
fork.condition $ limit.cone $ parallel_pair f g

/-- The equalizer built from `equalizer.ι f g` is limiting. -/
def equalizer_is_equalizer : is_limit (fork.of_ι (equalizer.ι f g) (equalizer.condition f g)) :=
is_limit.of_iso_limit (limit.is_limit _) (fork.ext (iso.refl _) (by tidy))

variables {f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the equalizer of `f` and `g`
    via `equalizer.lift : W ⟶ equalizer f g`. -/
abbreviation equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
limit.lift (parallel_pair f g) (fork.of_ι k h)

@[simp, reassoc]
lemma equalizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
  equalizer.lift k h ≫ equalizer.ι f g = k :=
limit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ equalizer f g`
    satisfying `l ≫ equalizer.ι f g = k`. -/
def equalizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
  {l : W ⟶ equalizer f g // l ≫ equalizer.ι f g = k} :=
⟨equalizer.lift k h, equalizer.lift_ι _ _⟩

/-- Two maps into an equalizer are equal if they are are equal when composed with the equalizer
    map. -/
@[ext] lemma equalizer.hom_ext {W : C} {k l : W ⟶ equalizer f g}
  (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
fork.is_limit.hom_ext (limit.is_limit _) h

/-- An equalizer morphism is a monomorphism -/
instance equalizer.ι_mono : mono (equalizer.ι f g) :=
{ right_cancellation := λ Z h k w, equalizer.hom_ext w }

end

section
variables {f g}
/-- The equalizer morphism in any limit cone is a monomorphism. -/
lemma mono_of_is_limit_parallel_pair {c : cone (parallel_pair f g)} (i : is_limit c) :
  mono (fork.ι c) :=
{ right_cancellation := λ Z h k w, fork.is_limit.hom_ext i w }

end

section
variables {f g}

/-- The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g`. -/
def id_fork (h : f = g) : fork f g :=
fork.of_ι (𝟙 X) $ h ▸ rfl

/-- The identity on `X` is an equalizer of `(f, g)`, if `f = g`. -/
def is_limit_id_fork (h : f = g) : is_limit (id_fork h) :=
fork.is_limit.mk _
  (λ s, fork.ι s)
  (λ s, category.comp_id _)
  (λ s m h, by { convert h zero, exact (category.comp_id _).symm })

/-- Every equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
lemma is_iso_limit_cone_parallel_pair_of_eq (h₀ : f = g) {c : cone (parallel_pair f g)}
  (h : is_limit c) : is_iso (c.π.app zero) :=
is_iso.of_iso $ is_limit.cone_point_unique_up_to_iso h $ is_limit_id_fork h₀

/-- The equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
lemma equalizer.ι_of_eq [has_equalizer f g] (h : f = g) : is_iso (equalizer.ι f g) :=
is_iso_limit_cone_parallel_pair_of_eq h $ limit.is_limit _

/-- Every equalizer of `(f, f)` is an isomorphism. -/
lemma is_iso_limit_cone_parallel_pair_of_self {c : cone (parallel_pair f f)} (h : is_limit c) :
  is_iso (c.π.app zero) :=
is_iso_limit_cone_parallel_pair_of_eq rfl h

/-- An equalizer that is an epimorphism is an isomorphism. -/
lemma is_iso_limit_cone_parallel_pair_of_epi {c : cone (parallel_pair f g)}
  (h : is_limit c) [epi (c.π.app zero)] : is_iso (c.π.app zero) :=
is_iso_limit_cone_parallel_pair_of_eq ((cancel_epi _).1 (fork.condition c)) h

end

instance has_equalizer_of_self : has_equalizer f f :=
has_limit.mk
{ cone := id_fork rfl,
  is_limit := is_limit_id_fork rfl }

/-- The equalizer inclusion for `(f, f)` is an isomorphism. -/
instance equalizer.ι_of_self : is_iso (equalizer.ι f f) :=
equalizer.ι_of_eq rfl

/-- The equalizer of a morphism with itself is isomorphic to the source. -/
def equalizer.iso_source_of_self : equalizer f f ≅ X :=
as_iso (equalizer.ι f f)

@[simp] lemma equalizer.iso_source_of_self_hom :
  (equalizer.iso_source_of_self f).hom = equalizer.ι f f :=
rfl

@[simp] lemma equalizer.iso_source_of_self_inv :
  (equalizer.iso_source_of_self f).inv = equalizer.lift (𝟙 X) (by simp) :=
by { ext, simp [equalizer.iso_source_of_self], }

section
/--
`has_coequalizer f g` represents a particular choice of colimiting cocone
for the parallel pair of morphisms `f` and `g`.
-/
abbreviation has_coequalizer := has_colimit (parallel_pair f g)

variables [has_coequalizer f g]

/-- If a coequalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `coequalizer f g`. -/
abbreviation coequalizer : C := colimit (parallel_pair f g)

/--  If a coequalizer of `f` and `g` exists, we can access the corresponding projection by
    saying `coequalizer.π f g`. -/
abbreviation coequalizer.π : Y ⟶ coequalizer f g :=
colimit.ι (parallel_pair f g) one

/--
An arbitrary choice of coequalizer cocone for a parallel pair `f` and `g`.
-/
abbreviation coequalizer.cofork : cofork f g := colimit.cocone (parallel_pair f g)

@[simp] lemma coequalizer.cofork_π :
  (coequalizer.cofork f g).π = coequalizer.π f g := rfl

@[simp] lemma coequalizer.cofork_ι_app_one :
  (coequalizer.cofork f g).ι.app one = coequalizer.π f g := rfl

@[reassoc] lemma coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
cofork.condition $ colimit.cocone $ parallel_pair f g

/-- The cofork built from `coequalizer.π f g` is colimiting. -/
def coequalizer_is_coequalizer :
  is_colimit (cofork.of_π (coequalizer.π f g) (coequalizer.condition f g)) :=
is_colimit.of_iso_colimit (colimit.is_colimit _) (cofork.ext (iso.refl _) (by tidy))

variables {f g}

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` factors through the coequalizer of `f`
    and `g` via `coequalizer.desc : coequalizer f g ⟶ W`. -/
abbreviation coequalizer.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : coequalizer f g ⟶ W :=
colimit.desc (parallel_pair f g) (cofork.of_π k h)

@[simp, reassoc]
lemma coequalizer.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
  coequalizer.π f g ≫ coequalizer.desc k h = k :=
colimit.ι_desc _ _

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` induces a morphism
    `l : coequalizer f g ⟶ W` satisfying `coequalizer.π ≫ g = l`. -/
def coequalizer.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
  {l : coequalizer f g ⟶ W // coequalizer.π f g ≫ l = k} :=
⟨coequalizer.desc k h, coequalizer.π_desc _ _⟩

/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
    map -/
@[ext] lemma coequalizer.hom_ext {W : C} {k l : coequalizer f g ⟶ W}
  (h : coequalizer.π f g ≫ k = coequalizer.π f g ≫ l) : k = l :=
cofork.is_colimit.hom_ext (colimit.is_colimit _) h

/-- A coequalizer morphism is an epimorphism -/
instance coequalizer.π_epi : epi (coequalizer.π f g) :=
{ left_cancellation := λ Z h k w, coequalizer.hom_ext w }

end

section
variables {f g}

/-- The coequalizer morphism in any colimit cocone is an epimorphism. -/
lemma epi_of_is_colimit_parallel_pair {c : cocone (parallel_pair f g)} (i : is_colimit c) :
  epi (c.ι.app one) :=
{ left_cancellation := λ Z h k w, cofork.is_colimit.hom_ext i w }

end

section
variables {f g}

/-- The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `f = g`. -/
def id_cofork (h : f = g) : cofork f g :=
cofork.of_π (𝟙 Y) $ h ▸ rfl

/-- The identity on `Y` is a coequalizer of `(f, g)`, where `f = g`.  -/
def is_colimit_id_cofork (h : f = g) : is_colimit (id_cofork h) :=
cofork.is_colimit.mk _
  (λ s, cofork.π s)
  (λ s, category.id_comp _)
  (λ s m h, by { convert h one, exact (category.id_comp _).symm })

/-- Every coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
lemma is_iso_colimit_cocone_parallel_pair_of_eq (h₀ : f = g) {c : cocone (parallel_pair f g)}
  (h : is_colimit c) : is_iso (c.ι.app one) :=
is_iso.of_iso $ is_colimit.cocone_point_unique_up_to_iso (is_colimit_id_cofork h₀) h

/-- The coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
lemma coequalizer.π_of_eq [has_coequalizer f g] (h : f = g) :
  is_iso (coequalizer.π f g) :=
is_iso_colimit_cocone_parallel_pair_of_eq h $ colimit.is_colimit _

/-- Every coequalizer of `(f, f)` is an isomorphism. -/
lemma is_iso_colimit_cocone_parallel_pair_of_self {c : cocone (parallel_pair f f)}
  (h : is_colimit c) : is_iso (c.ι.app one) :=
is_iso_colimit_cocone_parallel_pair_of_eq rfl h

/-- A coequalizer that is a monomorphism is an isomorphism. -/
lemma is_iso_limit_cocone_parallel_pair_of_epi {c : cocone (parallel_pair f g)}
  (h : is_colimit c) [mono (c.ι.app one)] : is_iso (c.ι.app one) :=
is_iso_colimit_cocone_parallel_pair_of_eq ((cancel_mono _).1 (cofork.condition c)) h

end

instance has_coequalizer_of_self : has_coequalizer f f :=
has_colimit.mk
{ cocone := id_cofork rfl,
  is_colimit := is_colimit_id_cofork rfl }

/-- The coequalizer projection for `(f, f)` is an isomorphism. -/
instance coequalizer.π_of_self : is_iso (coequalizer.π f f) :=
coequalizer.π_of_eq rfl

/-- The coequalizer of a morphism with itself is isomorphic to the target. -/
def coequalizer.iso_target_of_self : coequalizer f f ≅ Y :=
(as_iso (coequalizer.π f f)).symm

@[simp] lemma coequalizer.iso_target_of_self_hom :
  (coequalizer.iso_target_of_self f).hom = coequalizer.desc (𝟙 Y) (by simp) :=
by { ext, simp [coequalizer.iso_target_of_self], }

@[simp] lemma coequalizer.iso_target_of_self_inv :
  (coequalizer.iso_target_of_self f).inv = coequalizer.π f f :=
rfl

section comparison

variables {D : Type u₂} [category.{v} D] (G : C ⥤ D)

/--
The comparison morphism for the equalizer of `f,g`.
This is an isomorphism iff `G` preserves the equalizer of `f,g`; see
`category_theory/limits/preserves/shapes/equalizers.lean`
-/
def equalizer_comparison [has_equalizer f g] [has_equalizer (G.map f) (G.map g)] :
  G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
equalizer.lift (G.map (equalizer.ι _ _)) (by simp only [←G.map_comp, equalizer.condition])

@[simp, reassoc]
lemma equalizer_comparison_comp_π [has_equalizer f g] [has_equalizer (G.map f) (G.map g)] :
  equalizer_comparison f g G ≫ equalizer.ι (G.map f) (G.map g) = G.map (equalizer.ι f g) :=
equalizer.lift_ι _ _

@[simp, reassoc]
lemma map_lift_equalizer_comparison [has_equalizer f g] [has_equalizer (G.map f) (G.map g)]
  {Z : C} {h : Z ⟶ X} (w : h ≫ f = h ≫ g) :
    G.map (equalizer.lift h w) ≫ equalizer_comparison f g G =
      equalizer.lift (G.map h) (by simp only [←G.map_comp, w]) :=
by { ext, simp [← G.map_comp] }

/-- The comparison morphism for the coequalizer of `f,g`. -/
def coequalizer_comparison [has_coequalizer f g] [has_coequalizer (G.map f) (G.map g)] :
  coequalizer (G.map f) (G.map g) ⟶ G.obj (coequalizer f g) :=
coequalizer.desc (G.map (coequalizer.π _ _)) (by simp only [←G.map_comp, coequalizer.condition])

@[simp, reassoc]
lemma ι_comp_coequalizer_comparison [has_coequalizer f g] [has_coequalizer (G.map f) (G.map g)] :
  coequalizer.π _ _ ≫ coequalizer_comparison f g G = G.map (coequalizer.π _ _) :=
coequalizer.π_desc _ _

@[simp, reassoc]
lemma coequalizer_comparison_map_desc [has_coequalizer f g] [has_coequalizer (G.map f) (G.map g)]
  {Z : C} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) :
  coequalizer_comparison f g G ≫ G.map (coequalizer.desc h w) =
    coequalizer.desc (G.map h) (by simp only [←G.map_comp, w]) :=
by { ext, simp [← G.map_comp] }

end comparison

variables (C)

/-- `has_equalizers` represents a choice of equalizer for every pair of morphisms -/
abbreviation has_equalizers := has_limits_of_shape walking_parallel_pair C

/-- `has_coequalizers` represents a choice of coequalizer for every pair of morphisms -/
abbreviation has_coequalizers := has_colimits_of_shape walking_parallel_pair C

/-- If `C` has all limits of diagrams `parallel_pair f g`, then it has all equalizers -/
lemma has_equalizers_of_has_limit_parallel_pair
  [Π {X Y : C} {f g : X ⟶ Y}, has_limit (parallel_pair f g)] : has_equalizers C :=
{ has_limit := λ F, has_limit_of_iso (diagram_iso_parallel_pair F).symm }

/-- If `C` has all colimits of diagrams `parallel_pair f g`, then it has all coequalizers -/
lemma has_coequalizers_of_has_colimit_parallel_pair
  [Π {X Y : C} {f g : X ⟶ Y}, has_colimit (parallel_pair f g)] : has_coequalizers C :=
{ has_colimit := λ F, has_colimit_of_iso (diagram_iso_parallel_pair F) }


section
-- In this section we show that a split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
variables {C} [split_mono f]

/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `split_mono_equalizes` that it is a limit cone.
-/
@[simps {rhs_md := semireducible}]
def cone_of_split_mono : cone (parallel_pair (𝟙 Y) (retraction f ≫ f)) :=
fork.of_ι f (by simp)


/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
-/
def split_mono_equalizes {X Y : C} (f : X ⟶ Y) [split_mono f] : is_limit (cone_of_split_mono f) :=
fork.is_limit.mk' _ $ λ s,
⟨s.ι ≫ retraction f,
 by { dsimp, rw [category.assoc, ←s.condition], apply category.comp_id },
 λ m hm, by simp [←hm]⟩

end

section
-- In this section we show that a split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
variables {C} [split_epi f]

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `split_epi_coequalizes` that it is a colimit cocone.
-/
@[simps {rhs_md := semireducible}]
def cocone_of_split_epi : cocone (parallel_pair (𝟙 X) (f ≫ section_ f)) :=
cofork.of_π f (by simp)

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
-/
def split_epi_coequalizes {X Y : C} (f : X ⟶ Y) [split_epi f] :
  is_colimit (cocone_of_split_epi f) :=
cofork.is_colimit.mk' _ $ λ s,
⟨section_ f ≫ s.π,
 by { dsimp, rw [← category.assoc, ← s.condition, category.id_comp] },
 λ m hm, by simp [← hm]⟩

end

end category_theory.limits
