/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.fintype.basic
import category_theory.limits.limits
import category_theory.limits.shapes.finite_limits
import category_theory.sparse

/-!
# Wide pullbacks

We define the category `wide_pullback_shape`, (resp. `wide_pushout_shape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wide_cospan` (`wide_span`) constructs a functor from this category, hitting
the given morphisms.

We use `wide_pullback_shape` to define ordinary pullbacks (pushouts) by using `J := walking_pair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `has_wide_pullbacks` and `has_finite_wide_pullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/

universes v u

open category_theory category_theory.limits

variable (J : Type v)

/-- A wide pullback shape for any type `J` can be written simply as `option J`. -/
@[derive inhabited]
def wide_pullback_shape := option J

/-- A wide pushout shape for any type `J` can be written simply as `option J`. -/
@[derive inhabited]
def wide_pushout_shape := option J

namespace wide_pullback_shape

instance fintype_obj [fintype J] : fintype (wide_pullback_shape J) :=
by { rw wide_pullback_shape, apply_instance }

variable {J}

/-- The type of arrows for the shape indexing a wide pullback. -/
@[derive decidable_eq]
inductive hom : wide_pullback_shape J → wide_pullback_shape J → Type v
| id : Π X, hom X X
| term : Π (j : J), hom (some j) none

attribute [nolint unused_arguments] hom.decidable_eq

instance struct : category_struct (wide_pullback_shape J) :=
{ hom := hom,
  id := λ j, hom.id j,
  comp := λ j₁ j₂ j₃ f g,
  begin
    cases f,
      exact g,
    cases g,
    apply hom.term _
  end }

instance hom.inhabited : inhabited (hom none none) := ⟨hom.id (none : wide_pullback_shape J)⟩

local attribute [tidy] tactic.case_bash

instance fintype_hom [decidable_eq J] (j j' : wide_pullback_shape J) :
  fintype (j ⟶ j') :=
{ elems :=
  begin
    cases j',
    { cases j,
      { exact {hom.id none} },
      { exact {hom.term j} } },
    { by_cases some j' = j,
      { rw h,
        exact {hom.id j} },
      { exact ∅ } }
  end,
  complete := by tidy }

instance subsingleton_hom (j j' : wide_pullback_shape J) : subsingleton (j ⟶ j') :=
⟨by tidy⟩

instance category : small_category (wide_pullback_shape J) := sparse_category

instance fin_category [fintype J] [decidable_eq J] : fin_category (wide_pullback_shape J) :=
{ fintype_hom := wide_pullback_shape.fintype_hom }

@[simp] lemma hom_id (X : wide_pullback_shape J) : hom.id X = 𝟙 X := rfl

variables {C : Type u} [category.{v} C]

/--
Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simps]
def wide_cospan (B : C) (objs : J → C) (arrows : Π (j : J), objs j ⟶ B) : wide_pullback_shape J ⥤ C :=
{ obj := λ j, option.cases_on j B objs,
  map := λ X Y f,
  begin
    cases f with _ j,
    { apply (𝟙 _) },
    { exact arrows j }
  end }

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_cospan` -/
def diagram_iso_wide_cospan (F : wide_pullback_shape J ⥤ C) :
  F ≅ wide_cospan (F.obj none) (λ j, F.obj (some j)) (λ j, F.map (hom.term j)) :=
nat_iso.of_components (λ j, eq_to_iso $ by tidy) $ by tidy

end wide_pullback_shape

namespace wide_pushout_shape

instance fintype_obj [fintype J] : fintype (wide_pushout_shape J) :=
by { rw wide_pushout_shape, apply_instance }

variable {J}

/-- The type of arrows for the shape indexing a wide psuhout. -/
@[derive decidable_eq]
inductive hom : wide_pushout_shape J → wide_pushout_shape J → Type v
| id : Π X, hom X X
| init : Π (j : J), hom none (some j)

attribute [nolint unused_arguments] hom.decidable_eq

instance struct : category_struct (wide_pushout_shape J) :=
{ hom := hom,
  id := λ j, hom.id j,
  comp := λ j₁ j₂ j₃ f g,
  begin
    cases f,
      exact g,
    cases g,
    apply hom.init _
  end }

instance hom.inhabited : inhabited (hom none none) := ⟨hom.id (none : wide_pushout_shape J)⟩

local attribute [tidy] tactic.case_bash

instance fintype_hom [decidable_eq J] (j j' : wide_pushout_shape J) :
  fintype (j ⟶ j') :=
{ elems :=
  begin
    cases j,
    { cases j',
      { exact {hom.id none} },
      { exact {hom.init j'} } },
    { by_cases some j = j',
      { rw h,
        exact {hom.id j'} },
      { exact ∅ } }
  end,
  complete := by tidy }

instance subsingleton_hom (j j' : wide_pushout_shape J) : subsingleton (j ⟶ j') :=
⟨by tidy⟩

instance category : small_category (wide_pushout_shape J) := sparse_category

instance fin_category [fintype J] [decidable_eq J] : fin_category (wide_pushout_shape J) :=
{ fintype_hom := wide_pushout_shape.fintype_hom }

@[simp] lemma hom_id (X : wide_pushout_shape J) : hom.id X = 𝟙 X := rfl

variables {C : Type u} [category.{v} C]

/--
Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simps]
def wide_span (B : C) (objs : J → C) (arrows : Π (j : J), B ⟶ objs j) : wide_pushout_shape J ⥤ C :=
{ obj := λ j, option.cases_on j B objs,
  map := λ X Y f,
  begin
    cases f with _ j,
    { apply (𝟙 _) },
    { exact arrows j }
  end }

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_span` -/
def diagram_iso_wide_span (F : wide_pushout_shape J ⥤ C) :
  F ≅ wide_span (F.obj none) (λ j, F.obj (some j)) (λ j, F.map (hom.init j)) :=
nat_iso.of_components (λ j, eq_to_iso $ by tidy) $ by tidy

end wide_pushout_shape

variables (C : Type u) [category.{v} C]

/-- `has_wide_pullbacks` represents a choice of wide pullback for every collection of morphisms -/
class has_wide_pullbacks :=
(has_limits_of_shape : Π (J : Type v), has_limits_of_shape (wide_pullback_shape J) C)

/-- `has_wide_pullbacks` represents a choice of wide pullback for every finite collection of morphisms -/
class has_finite_wide_pullbacks :=
(has_limits_of_shape : Π (J : Type v) [decidable_eq J] [fintype J], has_limits_of_shape (wide_pullback_shape J) C)

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits, it also has finite wide pullbacks -/
def has_finite_wide_pullbacks_of_has_finite_limits [has_finite_limits C] : has_finite_wide_pullbacks C :=
{ has_limits_of_shape := λ J _ _, by exactI (has_finite_limits.has_limits_of_shape _) }

attribute [instance] has_wide_pullbacks.has_limits_of_shape
attribute [instance] has_finite_wide_pullbacks.has_limits_of_shape

/-- `has_wide_pushouts` represents a choice of wide pushout for every collection of morphisms -/
class has_wide_pushouts :=
(has_limits_of_shape : Π (J : Type v), has_limits_of_shape (wide_pushout_shape J) C)

/-- `has_wide_pushouts` represents a choice of wide pushout for every finite collection of morphisms -/
class has_finite_wide_pushouts :=
(has_limits_of_shape : Π (J : Type v) [decidable_eq J] [fintype J], has_limits_of_shape (wide_pushout_shape J) C)

/-- Finite wide pushouts are finite limits, so if `C` has all finite limits, it also has finite wide pushouts -/
def has_finite_wide_pushouts_of_has_finite_limits [has_finite_limits C] : has_finite_wide_pushouts C :=
{ has_limits_of_shape := λ J _ _, by exactI (has_finite_limits.has_limits_of_shape _) }

attribute [instance] has_wide_pushouts.has_limits_of_shape
attribute [instance] has_finite_wide_pushouts.has_limits_of_shape
