/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.fintype.basic
import category_theory.limits.limits
import category_theory.limits.shapes.finite_limits
import category_theory.sparse
import category_theory.punit
-- import category_theory.connected

universes v u

open category_theory category_theory.limits

variable (J : Type v)

/-- A wide pullback shape for any type `J` can be written simply as `option J`. -/
@[derive inhabited]
def wide_pullback_shape := option J

namespace wide_pullback_shape

local attribute [tidy] tactic.case_bash

instance fintype_obj [fintype J] : fintype (wide_pullback_shape J) :=
by { rw wide_pullback_shape, apply_instance }

variable {J}

/-- The type of arrows for the shape indexing a wide pullback. -/
@[derive decidable_eq]
inductive hom : wide_pullback_shape J → wide_pullback_shape J → Type v
| id : Π X, hom X X
| term : Π (j : J), hom (some j) none

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

instance : inhabited (hom none none) := ⟨hom.id (none : wide_pullback_shape J)⟩

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

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

local attribute [tidy] tactic.case_bash

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
nat_iso.of_components (λ j, eq_to_iso $ by cases j; tidy) $ by tidy

end wide_pullback_shape

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- `has_wide_pullbacks` represents a choice of wide pullback for every collection of morphisms -/
class has_wide_pullbacks :=
(has_limits_of_shape : Π (J : Type v), has_limits_of_shape.{v} (wide_pullback_shape J) C)

/-- `has_wide_pullbacks` represents a choice of wide pullback for every finite collection of morphisms -/
class has_finite_wide_pullbacks :=
(has_limits_of_shape : Π (J : Type v) [decidable_eq J] [fintype J], has_limits_of_shape.{v} (wide_pullback_shape J) C)

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits, it also has finite wide pullbacks -/
def has_finite_wide_pullbacks_of_has_finite_limits [has_finite_limits.{v} C] : has_finite_wide_pullbacks.{v} C :=
{ has_limits_of_shape := λ J _ _, by exactI (has_finite_limits.has_limits_of_shape _) }

attribute [instance] has_wide_pullbacks.has_limits_of_shape
attribute [instance] has_finite_wide_pullbacks.has_limits_of_shape
