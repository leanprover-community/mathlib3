/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.epi_mono
import category_theory.limits.limits

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
* `is_iso_limit_cone_parallel_pair_of_self` states that the identity on the domain of `f` is an equalizer
  of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

open category_theory

namespace category_theory.limits

local attribute [tidy] tactic.case_bash

universes v u

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
def parallel_pair (f g : X ⟶ Y) : walking_parallel_pair ⥤ C :=
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
def diagram_iso_parallel_pair (F : walking_parallel_pair ⥤ C) :
  F ≅ parallel_pair (F.map left) (F.map right) :=
nat_iso.of_components (λ j, eq_to_iso $ by cases j; tidy) $ by tidy

/-- A fork on `f` and `g` is just a `cone (parallel_pair f g)`. -/
abbreviation fork (f g : X ⟶ Y) := cone (parallel_pair f g)

/-- A cofork on `f` and `g` is just a `cocone (parallel_pair f g)`. -/
abbreviation cofork (f g : X ⟶ Y) := cocone (parallel_pair f g)

variables {f g : X ⟶ Y}

@[simp, reassoc] lemma fork.app_zero_left (s : fork f g) :
  (s.π).app zero ≫ f = (s.π).app one :=
by rw [←s.w left, parallel_pair_map_left]

@[simp, reassoc] lemma fork.app_zero_right (s : fork f g) :
  (s.π).app zero ≫ g = (s.π).app one :=
by rw [←s.w right, parallel_pair_map_right]

@[simp, reassoc] lemma cofork.left_app_one (s : cofork f g) :
  f ≫ (s.ι).app one = (s.ι).app zero :=
by rw [←s.w left, parallel_pair_map_left]

@[simp, reassoc] lemma cofork.right_app_one (s : cofork f g) :
  g ≫ (s.ι).app one = (s.ι).app zero :=
by rw [←s.w right, parallel_pair_map_right]

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
def fork.of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork f g :=
{ X := P,
  π :=
  { app := λ X, begin cases X, exact ι, exact ι ≫ f, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      { dsimp, simp, }, -- TODO If someone could decipher why these aren't done on the previous line, that would be great
      { exact w },
      { dsimp, simp, }, -- TODO idem
    end } }

/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
    `f ≫ π = g ≫ π`. -/
def cofork.of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : cofork f g :=
{ X := P,
  ι :=
  { app := λ X, begin cases X, exact f ≫ π, exact π, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      { dsimp, simp, }, -- TODO idem
      { exact w.symm },
      { dsimp, simp, }, -- TODO idem
    end } }

@[simp] lemma fork.of_ι_app_zero {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app zero = ι := rfl
@[simp] lemma fork.of_ι_app_one {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app one = ι ≫ f := rfl
@[simp] lemma cofork.of_π_app_zero {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  (cofork.of_π π w).ι.app zero = f ≫ π := rfl
@[simp] lemma cofork.of_π_app_one {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  (cofork.of_π π w).ι.app one = π := rfl

/-- A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms `t.π.app zero : t.X ⟶ X`
    and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is interesting, and we give it the
    shorter name `fork.ι t`. -/
abbreviation fork.ι (t : fork f g) := t.π.app zero

/-- A cofork `t` on the parallel_pair `f g : X ⟶ Y` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `cofork.π t`. -/
abbreviation cofork.π (t : cofork f g) := t.ι.app one

@[simp] lemma fork.ι_of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  fork.ι (fork.of_ι ι w) = ι := rfl
@[simp] lemma cofork.π_of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  cofork.π (cofork.of_π π w) = π := rfl

lemma fork.ι_eq_app_zero (t : fork f g) : fork.ι t = t.π.app zero := rfl
lemma cofork.π_eq_app_one (t : cofork f g) : cofork.π t = t.ι.app one := rfl

lemma fork.condition (t : fork f g) : (fork.ι t) ≫ f = (fork.ι t) ≫ g :=
begin
  erw [t.w left, ← t.w right], refl
end
lemma cofork.condition (t : cofork f g) : f ≫ (cofork.π t) = g ≫ (cofork.π t) :=
begin
  erw [t.w left, ← t.w right], refl
end

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

def fork.mk_hom {s t : fork f g} (k : s.X ⟶ t.X) (w : k ≫ t.ι = s.ι) : s ⟶ t :=
{ hom := k,
  w' :=
  begin
    rintro ⟨_|_⟩,
    exact w,
    simpa using w =≫ f,
  end }

variables (f g)

section
variables [has_limit (parallel_pair f g)]

/-- If we have chosen an equalizer of `f` and `g`, we can access the corresponding object by
    saying `equalizer f g`. -/
abbreviation equalizer : C := limit (parallel_pair f g)

/-- If we have chosen an equalizer of `f` and `g`, we can access the inclusion
    `equalizer f g ⟶ X` by saying `equalizer.ι f g`. -/
abbreviation equalizer.ι : equalizer f g ⟶ X :=
limit.π (parallel_pair f g) zero

abbreviation equalizer.fork : fork f g := limit.cone (parallel_pair f g)

@[simp] lemma equalizer.fork_ι :
  (equalizer.fork f g).ι = equalizer.ι f g := rfl

@[simp] lemma equalizer.fork_π_app_zero :
  (equalizer.fork f g).π.app zero = equalizer.ι f g := rfl

@[reassoc] lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
fork.condition $ limit.cone $ parallel_pair f g

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
def is_iso_limit_cone_parallel_pair_of_eq (h₀ : f = g) {c : cone (parallel_pair f g)}
  (h : is_limit c) : is_iso (c.π.app zero) :=
is_iso.of_iso $ is_limit.cone_point_unique_up_to_iso h $ is_limit_id_fork h₀

/-- The equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
def equalizer.ι_of_eq [has_limit (parallel_pair f g)] (h : f = g) : is_iso (equalizer.ι f g) :=
is_iso_limit_cone_parallel_pair_of_eq h $ limit.is_limit _

/-- Every equalizer of `(f, f)` is an isomorphism. -/
def is_iso_limit_cone_parallel_pair_of_self {c : cone (parallel_pair f f)} (h : is_limit c) :
  is_iso (c.π.app zero) :=
is_iso_limit_cone_parallel_pair_of_eq rfl h

/-- An equalizer that is an epimorphism is an isomorphism. -/
def is_iso_limit_cone_parallel_pair_of_epi {c : cone (parallel_pair f g)}
  (h : is_limit c) [epi (c.π.app zero)] : is_iso (c.π.app zero) :=
is_iso_limit_cone_parallel_pair_of_eq ((cancel_epi _).1 (fork.condition c)) h

end

/-- The equalizer inclusion for `(f, f)` is an isomorphism. -/
instance equalizer.ι_of_self [has_limit (parallel_pair f f)] : is_iso (equalizer.ι f f) :=
equalizer.ι_of_eq rfl

/-- The equalizer of a morphism with itself is isomorphic to the source. -/
def equalizer.iso_source_of_self [has_limit (parallel_pair f f)] : equalizer f f ≅ X :=
as_iso (equalizer.ι f f)

@[simp] lemma equalizer.iso_source_of_self_hom [has_limit (parallel_pair f f)] :
  (equalizer.iso_source_of_self f).hom = equalizer.ι f f :=
rfl

@[simp] lemma equalizer.iso_source_of_self_inv [has_limit (parallel_pair f f)] :
  (equalizer.iso_source_of_self f).inv = equalizer.lift (𝟙 X) (by simp) :=
rfl

section
variables [has_colimit (parallel_pair f g)]

/-- If we have chosen a coequalizer of `f` and `g`, we can access the corresponding object by
    saying `coequalizer f g`. -/
abbreviation coequalizer := colimit (parallel_pair f g)

/-- If we have chosen a coequalizer of `f` and `g`, we can access the corresponding projection by
    saying `coequalizer.π f g`. -/
abbreviation coequalizer.π : Y ⟶ coequalizer f g :=
colimit.ι (parallel_pair f g) one

@[simp] lemma coequalizer.π.cofork :
  cofork.π (colimit.cocone (parallel_pair f g)) = coequalizer.π f g := rfl

@[simp] lemma coequalizer.π.eq_app_one :
  (colimit.cocone (parallel_pair f g)).ι.app one = coequalizer.π f g := rfl

@[reassoc] lemma coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
cofork.condition $ colimit.cocone $ parallel_pair f g

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
def is_iso_colimit_cocone_parallel_pair_of_eq (h₀ : f = g) {c : cocone (parallel_pair f g)}
  (h : is_colimit c) : is_iso (c.ι.app one) :=
is_iso.of_iso $ is_colimit.cocone_point_unique_up_to_iso (is_colimit_id_cofork h₀) h

/-- The coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
def coequalizer.π_of_eq [has_colimit (parallel_pair f g)] (h : f = g) :
  is_iso (coequalizer.π f g) :=
is_iso_colimit_cocone_parallel_pair_of_eq h $ colimit.is_colimit _

/-- Every coequalizer of `(f, f)` is an isomorphism. -/
def is_iso_colimit_cocone_parallel_pair_of_self {c : cocone (parallel_pair f f)}
  (h : is_colimit c) : is_iso (c.ι.app one) :=
is_iso_colimit_cocone_parallel_pair_of_eq rfl h

/-- A coequalizer that is a monomorphism is an isomorphism. -/
def is_iso_limit_cocone_parallel_pair_of_epi {c : cocone (parallel_pair f g)}
  (h : is_colimit c) [mono (c.ι.app one)] : is_iso (c.ι.app one) :=
is_iso_colimit_cocone_parallel_pair_of_eq ((cancel_mono _).1 (cofork.condition c)) h

end

/-- The coequalizer projection for `(f, f)` is an isomorphism. -/
instance coequalizer.π_of_self [has_colimit (parallel_pair f f)] : is_iso (coequalizer.π f f) :=
coequalizer.π_of_eq rfl

/-- The coequalizer of a morphism with itself is isomorphic to the target. -/
def coequalizer.iso_target_of_self [has_colimit (parallel_pair f f)] : coequalizer f f ≅ Y :=
(as_iso (coequalizer.π f f)).symm

@[simp] lemma coequalizer.iso_target_of_self_hom [has_colimit (parallel_pair f f)] :
  (coequalizer.iso_target_of_self f).hom = coequalizer.desc (𝟙 Y) (by simp) :=
rfl

@[simp] lemma coequalizer.iso_target_of_self_inv [has_colimit (parallel_pair f f)] :
  (coequalizer.iso_target_of_self f).inv = coequalizer.π f f :=
rfl

variables (C)

/-- `has_equalizers` represents a choice of equalizer for every pair of morphisms -/
class has_equalizers :=
(has_limits_of_shape : has_limits_of_shape walking_parallel_pair C)

/-- `has_coequalizers` represents a choice of coequalizer for every pair of morphisms -/
class has_coequalizers :=
(has_colimits_of_shape : has_colimits_of_shape walking_parallel_pair C)

attribute [instance] has_equalizers.has_limits_of_shape has_coequalizers.has_colimits_of_shape

/-- If `C` has all limits of diagrams `parallel_pair f g`, then it has all equalizers -/
def has_equalizers_of_has_limit_parallel_pair
  [Π {X Y : C} {f g : X ⟶ Y}, has_limit (parallel_pair f g)] : has_equalizers C :=
{ has_limits_of_shape := { has_limit := λ F, has_limit_of_iso (diagram_iso_parallel_pair F).symm } }

/-- If `C` has all colimits of diagrams `parallel_pair f g`, then it has all coequalizers -/
def has_coequalizers_of_has_colimit_parallel_pair
  [Π {X Y : C} {f g : X ⟶ Y}, has_colimit (parallel_pair f g)] : has_coequalizers C :=
{ has_colimits_of_shape := { has_colimit := λ F, has_colimit_of_iso (diagram_iso_parallel_pair F) } }

section
-- In this section we show that a split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
variables {C} [split_mono f]

/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `split_mono_equalizes` that it is a limit cone.
-/
def cone_of_split_mono : cone (parallel_pair (𝟙 Y) (retraction f ≫ f)) :=
fork.of_ι f (by tidy)

@[simp] lemma cone_of_split_mono_π_app_zero : (cone_of_split_mono f).π.app zero = f := rfl
@[simp] lemma cone_of_split_mono_π_app_one : (cone_of_split_mono f).π.app one = f ≫ 𝟙 Y := rfl

/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
-/
def split_mono_equalizes {X Y : C} (f : X ⟶ Y) [split_mono f] : is_limit (cone_of_split_mono f) :=
{ lift := λ s, s.π.app zero ≫ retraction f,
  fac' := λ s,
  begin
    rintros (⟨⟩|⟨⟩),
    { rw [cone_of_split_mono_π_app_zero],
      erw [category.assoc, ← s.π.naturality right, s.π.naturality left, category.comp_id], },
    { erw [cone_of_split_mono_π_app_one, category.comp_id, category.assoc,
            ← s.π.naturality right, category.id_comp], }
  end,
  uniq' := λ s m w, begin rw ←(w zero), simp, end, }

end

section
-- In this section we show that a split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
variables {C} [split_epi f]

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `split_epi_coequalizes` that it is a colimit cocone.
-/
def cocone_of_split_epi : cocone (parallel_pair (𝟙 X) (f ≫ section_ f)) :=
cofork.of_π f (by tidy)

@[simp] lemma cocone_of_split_epi_ι_app_one : (cocone_of_split_epi f).ι.app one = f := rfl
@[simp] lemma cocone_of_split_epi_ι_app_zero : (cocone_of_split_epi f).ι.app zero = 𝟙 X ≫ f := rfl

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
-/
def split_epi_coequalizes {X Y : C} (f : X ⟶ Y) [split_epi f] : is_colimit (cocone_of_split_epi f) :=
{ desc := λ s, section_ f ≫ s.ι.app one,
  fac' := λ s,
  begin
    rintros (⟨⟩|⟨⟩),
    { erw [cocone_of_split_epi_ι_app_zero, category.assoc, category.id_comp, ←category.assoc,
            s.ι.naturality right, functor.const.obj_map, category.comp_id], },
    { erw [cocone_of_split_epi_ι_app_one, ←category.assoc, s.ι.naturality right,
            ←s.ι.naturality left, category.id_comp] }
  end,
  uniq' := λ s m w, begin rw ←(w one), simp, end, }

end

end category_theory.limits
