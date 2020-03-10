/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import data.fintype
import category_theory.limits.limits
import category_theory.limits.shapes.finite_limits

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
* `is_limit_cone_parallel_pair_self` states that the identity on the domain of `f` is an equalizer
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
@[derive decidable_eq] inductive walking_parallel_pair : Type v
| zero | one

instance fintype_walking_parallel_pair : fintype walking_parallel_pair :=
{ elems := [walking_parallel_pair.zero, walking_parallel_pair.one].to_finset,
  complete := λ x, by { cases x; simp } }

open walking_parallel_pair

/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
@[derive _root_.decidable_eq] inductive walking_parallel_pair_hom :
  walking_parallel_pair → walking_parallel_pair → Type v
| left : walking_parallel_pair_hom zero one
| right : walking_parallel_pair_hom zero one
| id : Π X : walking_parallel_pair.{v}, walking_parallel_pair_hom X X

open walking_parallel_pair_hom

instance (j j' : walking_parallel_pair) : fintype (walking_parallel_pair_hom j j') :=
{ elems := walking_parallel_pair.rec_on j
    (walking_parallel_pair.rec_on j' [walking_parallel_pair_hom.id zero].to_finset
      [left, right].to_finset)
    (walking_parallel_pair.rec_on j' ∅ [walking_parallel_pair_hom.id one].to_finset),
  complete := by tidy }

def walking_parallel_pair_hom.comp :
  Π (X Y Z : walking_parallel_pair)
    (f : walking_parallel_pair_hom X Y) (g : walking_parallel_pair_hom Y Z),
    walking_parallel_pair_hom X Z
  | _ _ _ (id _) h := h
  | _ _ _ left   (id one) := left
  | _ _ _ right  (id one) := right
.

instance walking_parallel_pair_hom_category : small_category.{v} walking_parallel_pair :=
{ hom  := walking_parallel_pair_hom,
  id   := walking_parallel_pair_hom.id,
  comp := walking_parallel_pair_hom.comp }

instance : fin_category.{v} walking_parallel_pair.{v} := { }

lemma walking_parallel_pair_hom_id (X : walking_parallel_pair.{v}) :
  walking_parallel_pair_hom.id X = 𝟙 X :=
rfl

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables {X Y : C}

def parallel_pair (f g : X ⟶ Y) : walking_parallel_pair.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | one := Y
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, left := f
  | _, _, right := g
  end }.

@[simp] lemma parallel_pair_map_left (f g : X ⟶ Y) : (parallel_pair f g).map left = f := rfl
@[simp] lemma parallel_pair_map_right (f g : X ⟶ Y) : (parallel_pair f g).map right = g := rfl

@[simp] lemma parallel_pair_functor_obj
  {F : walking_parallel_pair.{v} ⥤ C} (j : walking_parallel_pair.{v}) :
  (parallel_pair (F.map left) (F.map right)).obj j = F.obj j :=
begin
  cases j; refl
end

abbreviation fork (f g : X ⟶ Y) := cone (parallel_pair f g)
abbreviation cofork (f g : X ⟶ Y) := cocone (parallel_pair f g)

variables {f g : X ⟶ Y}

@[simp] lemma cone_parallel_pair_left (s : cone (parallel_pair f g)) :
  (s.π).app zero ≫ f = (s.π).app one :=
by { conv_lhs { congr, skip, rw ←parallel_pair_map_left f g }, rw s.w }

@[simp] lemma cone_parallel_pair_right (s : cone (parallel_pair f g)) :
  (s.π).app zero ≫ g = (s.π).app one :=
by { conv_lhs { congr, skip, rw ←parallel_pair_map_right f g }, rw s.w }

@[simp] lemma cocone_parallel_pair_left (s : cocone (parallel_pair f g)) :
  f ≫ (s.ι).app one = (s.ι).app zero :=
by { conv_lhs { congr, rw ←parallel_pair_map_left f g }, rw s.w }

@[simp] lemma cocone_parallel_pair_right (s : cocone (parallel_pair f g)) :
  g ≫ (s.ι).app one = (s.ι).app zero :=
by { conv_lhs { congr, rw ←parallel_pair_map_right f g }, rw s.w }

/-- To check whether two maps are equalized by both maps of a fork, it suffices to check it for the
    first map -/
lemma cone_parallel_pair_ext (s : cone (parallel_pair f g)) {W : C} {k l : W ⟶ s.X}
  (h : k ≫ s.π.app zero = l ≫ s.π.app zero) : ∀ (j : walking_parallel_pair),
    k ≫ s.π.app j = l ≫ s.π.app j
| zero := h
| one := by { rw [←cone_parallel_pair_left, ←category.assoc, ←category.assoc], congr, exact h }

/-- To check whether two maps are coequalized by both maps of a cofork, it suffices to check it for
    the second map -/
lemma cocone_parallel_pair_ext (s : cocone (parallel_pair f g)) {W : C} {k l : s.X ⟶ W}
  (h : s.ι.app one ≫ k = s.ι.app one ≫ l) : ∀ (j : walking_parallel_pair),
    s.ι.app j ≫ k = s.ι.app j ≫ l
| zero := by { rw [←cocone_parallel_pair_right, category.assoc, category.assoc], congr, exact h }
| one := h

attribute [simp] walking_parallel_pair_hom_id

def fork.of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork f g :=
{ X := P,
  π :=
  { app := λ X, begin cases X, exact ι, exact ι ≫ f, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      exact w
    end } }
def cofork.of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : cofork f g :=
{ X := P,
  ι :=
  { app := λ X, begin cases X, exact f ≫ π, exact π, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      exact eq.symm w
    end } }

@[simp] lemma fork.of_ι_app_zero {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app zero = ι := rfl
@[simp] lemma fork.of_ι_app_one {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app one = ι ≫ f := rfl

def fork.ι (t : fork f g) := t.π.app zero
def cofork.π (t : cofork f g) := t.ι.app one
lemma fork.condition (t : fork f g) : (fork.ι t) ≫ f = (fork.ι t) ≫ g :=
begin
  erw [t.w left, ← t.w right], refl
end
lemma cofork.condition (t : cofork f g) : f ≫ (cofork.π t) = g ≫ (cofork.π t) :=
begin
  erw [t.w left, ← t.w right], refl
end

section
local attribute [ext] cone

/-- The fork induced by the ι map of some fork `t` is the same as `t` -/
lemma fork.eq_of_ι_ι (t : fork f g) : t = fork.of_ι (fork.ι t) (fork.condition t) :=
begin
  have h : t.π = (fork.of_ι (fork.ι t) (fork.condition t)).π,
  { ext j, cases j,
    { refl },
    { rw ←cone_parallel_pair_left, refl } },
  tidy
end

end

def cone.of_fork
  {F : walking_parallel_pair.{v} ⥤ C} (t : fork (F.map left) (F.map right)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g, by { cases j; cases j'; cases g; dsimp; simp } } }

section
local attribute [ext] cocone

/-- The cofork induced by the π map of some fork `t` is the same as `t` -/
lemma cofork.eq_of_π_π (t : cofork f g) : t = cofork.of_π (cofork.π t) (cofork.condition t) :=
begin
  have h : t.ι = (cofork.of_π (cofork.π t) (cofork.condition t)).ι,
  { ext j, cases j,
    { rw ←cocone_parallel_pair_left, refl },
    { refl } },
  tidy
end

end

def cocone.of_cofork
  {F : walking_parallel_pair.{v} ⥤ C} (t : cofork (F.map left) (F.map right)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g, by { cases j; cases j'; cases g; dsimp; simp } } }

@[simp] lemma cone.of_fork_π
  {F : walking_parallel_pair.{v} ⥤ C} (t : fork (F.map left) (F.map right)) (j) :
  (cone.of_fork t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

@[simp] lemma cocone.of_cofork_ι
  {F : walking_parallel_pair.{v} ⥤ C} (t : cofork (F.map left) (F.map right)) (j) :
  (cocone.of_cofork t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

def fork.of_cone
  {F : walking_parallel_pair.{v} ⥤ C} (t : cone F) : fork (F.map left) (F.map right) :=
{ X := t.X,
  π := { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }
def cofork.of_cocone
  {F : walking_parallel_pair.{v} ⥤ C} (t : cocone F) : cofork (F.map left) (F.map right) :=
{ X := t.X,
  ι := { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X } }

@[simp] lemma fork.of_cone_π {F : walking_parallel_pair.{v} ⥤ C} (t : cone F) (j) :
  (fork.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl
@[simp] lemma cofork.of_cocone_ι {F : walking_parallel_pair.{v} ⥤ C} (t : cocone F) (j) :
  (cofork.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

variables (f g)

section
variables [has_limit (parallel_pair f g)]

abbreviation equalizer := limit (parallel_pair f g)

abbreviation equalizer.ι : equalizer f g ⟶ X :=
limit.π (parallel_pair f g) zero

@[simp] lemma equalizer.ι.fork :
  fork.ι (limit.cone (parallel_pair f g)) = equalizer.ι f g := rfl

@[simp] lemma equalizer.ι.eq_app_zero :
  (limit.cone (parallel_pair f g)).π.app zero = equalizer.ι f g := rfl

@[reassoc] lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
fork.condition $ limit.cone $ parallel_pair f g

abbreviation equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
limit.lift (parallel_pair f g) (fork.of_ι k h)

/-- Two maps into an equalizer are equal if they are are equal when composed with the equalizer
    map. -/
@[ext] lemma equalizer.hom_ext {W : C} {k l : W ⟶ equalizer f g}
  (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
limit.hom_ext $ cone_parallel_pair_ext _ h

/-- An equalizer morphism is a monomorphism -/
lemma equalizer.ι_mono : mono (equalizer.ι f g) :=
{ right_cancellation := λ Z h k w, equalizer.hom_ext _ _ w }

end

section
/-- The identity determines a cone on the equalizer diagram of f and f -/
def cone_parallel_pair_self : cone (parallel_pair f f) :=
{ X := X,
  π :=
  { app := λ j, match j with | zero := 𝟙 X | one := f end } }

@[simp] lemma cone_parallel_pair_self_π_app_zero : (cone_parallel_pair_self f).π.app zero = 𝟙 X :=
rfl

@[simp] lemma cone_parallel_pair_self_X : (cone_parallel_pair_self f).X = X := rfl

/-- The identity on X is an equalizer of (f, f) -/
def is_limit_cone_parallel_pair_self : is_limit (cone_parallel_pair_self f) :=
{ lift := λ s, s.π.app zero,
  fac' := λ s j,
  match j with
  | zero := by erw category.comp_id
  | one := by erw cone_parallel_pair_left
  end,
  uniq' := λ s m w, by { convert w zero, erw category.comp_id } }

/-- Every equalizer of (f, f) is an isomorphism -/
def limit_cone_parallel_pair_self_is_iso (c : cone (parallel_pair f f)) (h : is_limit c) :
  is_iso (c.π.app zero) :=
  let c' := cone_parallel_pair_self f,
    z : c ≅ c' := is_limit.unique_up_to_iso h (is_limit_cone_parallel_pair_self f) in
  is_iso.of_iso (functor.map_iso (cones.forget _) z)

/-- The equalizer of (f, f) is an isomorphism -/
def equalizer.ι_of_self [has_limit (parallel_pair f f)] : is_iso (equalizer.ι f f) :=
limit_cone_parallel_pair_self_is_iso _ _ $ limit.is_limit _

/-- Every equalizer of (f, g), where f = g, is an isomorphism -/
def limit_cone_parallel_pair_self_is_iso' (c : cone (parallel_pair f g)) (h₀ : is_limit c)
  (h₁ : f = g) : is_iso (c.π.app zero) :=
begin
  rw fork.eq_of_ι_ι c at *,
  have h₂ : is_limit (fork.of_ι (c.π.app zero) rfl : fork f f), by convert h₀,
  exact limit_cone_parallel_pair_self_is_iso f (fork.of_ι (c.π.app zero) rfl) h₂
end

/-- The equalizer of (f, g), where f = g, is an isomorphism -/
def equalizer.ι_of_self' [has_limit (parallel_pair f g)] (h : f = g) : is_iso (equalizer.ι f g) :=
limit_cone_parallel_pair_self_is_iso' _ _ _ (limit.is_limit _) h

/-- An equalizer that is an epimorphism is an isomorphism -/
def epi_limit_cone_parallel_pair_is_iso (c : cone (parallel_pair f g))
  (h : is_limit c) [epi (c.π.app zero)] : is_iso (c.π.app zero) :=
limit_cone_parallel_pair_self_is_iso' f g c h $
  (cancel_epi (c.π.app zero)).1 (fork.condition c)

end

section
variables [has_colimit (parallel_pair f g)]

abbreviation coequalizer := colimit (parallel_pair f g)

abbreviation coequalizer.π : Y ⟶ coequalizer f g :=
colimit.ι (parallel_pair f g) one

@[simp] lemma coequalizer.π.cofork :
  cofork.π (colimit.cocone (parallel_pair f g)) = coequalizer.π f g := rfl

@[simp] lemma coequalizer.π.eq_app_one :
  (colimit.cocone (parallel_pair f g)).ι.app one = coequalizer.π f g := rfl

@[reassoc] lemma coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
cofork.condition $ colimit.cocone $ parallel_pair f g

abbreviation coequalizer.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : coequalizer f g ⟶ W :=
colimit.desc (parallel_pair f g) (cofork.of_π k h)

/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
    map -/
@[ext] lemma coequalizer.hom_ext {W : C} {k l : coequalizer f g ⟶ W}
  (h : coequalizer.π f g ≫ k = coequalizer.π f g ≫ l) : k = l :=
colimit.hom_ext $ cocone_parallel_pair_ext _ h

/-- A coequalizer morphism is an epimorphism -/
lemma coequalizer.π_epi : epi (coequalizer.π f g) :=
{ left_cancellation := λ Z h k w, coequalizer.hom_ext _ _ w }

end

section

/-- The identity determines a cocone on the coequalizer diagram of f and f -/
def cocone_parallel_pair_self : cocone (parallel_pair f f) :=
{ X := Y,
  ι :=
  { app := λ j, match j with | zero := f | one := 𝟙 Y end,
    naturality' := λ j j' g,
    begin
      cases g,
      { refl },
      { erw category.comp_id _ f },
      { dsimp, simp }
    end } }

@[simp] lemma cocone_parallel_pair_self_ι_app_one : (cocone_parallel_pair_self f).ι.app one = 𝟙 Y :=
rfl

@[simp] lemma cocone_parallel_pair_self_X : (cocone_parallel_pair_self f).X  = Y := rfl

/-- The identity on Y is a colimit of (f, f) -/
def is_colimit_cocone_parallel_pair_self : is_colimit (cocone_parallel_pair_self f) :=
{ desc := λ s, s.ι.app one,
  fac' := λ s j,
  match j with
  | zero := by erw cocone_parallel_pair_right
  | one := by erw category.id_comp
  end,
  uniq' := λ s m w, by { convert w one, erw category.id_comp } }

/-- Every coequalizer of (f, f) is an isomorphism -/
def colimit_cocone_parallel_pair_self_is_iso (c : cocone (parallel_pair f f)) (h : is_colimit c) :
  is_iso (c.ι.app one) :=
  let c' := cocone_parallel_pair_self f,
    z : c' ≅ c := is_colimit.unique_up_to_iso (is_colimit_cocone_parallel_pair_self f) h in
  is_iso.of_iso $ functor.map_iso (cocones.forget _) z

/-- The coequalizer of (f, f) is an isomorphism -/
def coequalizer.π_of_self [has_colimit (parallel_pair f f)] : is_iso (coequalizer.π f f) :=
colimit_cocone_parallel_pair_self_is_iso _ _ $ colimit.is_colimit _

/-- Every coequalizer of (f, g), where f = g, is an isomorphism -/
def colimit_cocone_parallel_pair_self_is_iso' (c : cocone (parallel_pair f g)) (h₀ : is_colimit c)
  (h₁ : f = g) : is_iso (c.ι.app one) :=
begin
  rw cofork.eq_of_π_π c at *,
  have h₂ : is_colimit (cofork.of_π (c.ι.app one) rfl : cofork f f), by convert h₀,
  exact colimit_cocone_parallel_pair_self_is_iso f (cofork.of_π (c.ι.app one) rfl) h₂
end

/-- The coequalizer of (f, g), where f = g, is an isomorphism -/
def coequalizer.π_of_self' [has_colimit (parallel_pair f g)] (h : f = g) :
  is_iso (coequalizer.π f g) :=
colimit_cocone_parallel_pair_self_is_iso' _ _ _ (colimit.is_colimit _) h

/-- A coequalizer that is a monomorphism is an isomorphism -/
def mono_limit_cocone_parallel_pair_is_iso (c : cocone (parallel_pair f g))
  (h : is_colimit c) [mono (c.ι.app one)] : is_iso (c.ι.app one) :=
colimit_cocone_parallel_pair_self_is_iso' f g c h $
  (cancel_mono (c.ι.app one)).1 (cofork.condition c)

end

variables (C)

/-- `has_equalizers` represents a choice of equalizer for every pair of morphisms -/
class has_equalizers :=
(has_limits_of_shape : has_limits_of_shape.{v} walking_parallel_pair C)

/-- `has_coequalizers` represents a choice of coequalizer for every pair of morphisms -/
class has_coequalizers :=
(has_colimits_of_shape : has_colimits_of_shape.{v} walking_parallel_pair C)

attribute [instance] has_equalizers.has_limits_of_shape has_coequalizers.has_colimits_of_shape

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
def has_equalizers_of_has_finite_limits [has_finite_limits.{v} C] : has_equalizers.{v} C :=
{ has_limits_of_shape := infer_instance }

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
def has_coequalizers_of_has_finite_colimits [has_finite_colimits.{v} C] : has_coequalizers.{v} C :=
{ has_colimits_of_shape := infer_instance }

end category_theory.limits
