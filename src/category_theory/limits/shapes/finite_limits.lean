/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.fin_category
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.wide_pullbacks
import category_theory.limits.shapes.pullbacks
import data.fintype.basic

/-!
# Categories with finite limits.

A typeclass for categories with all finite (co)limits.
-/

universes w' w v' u' v u

noncomputable theory

open category_theory

namespace category_theory.limits

variables (C : Type u) [category.{v} C]

/--
A category has all finite limits of size `w` if every functor `J ⥤ C` with a `fin_category J`
instance and `J : Type w` has a limit.

This is often called 'finitely complete'.
-/
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
class has_finite_limits_of_size : Prop :=
(out (J : Type w) [𝒥 : small_category J] [@fin_category J 𝒥] : @has_limits_of_shape J 𝒥 C _)

/-- Most often we will only require finite limits of size 0, so in `has_finite_limits` we
fix the universe level. -/
abbreviation has_finite_limits := has_finite_limits_of_size.{0}

@[priority 100]
instance has_limits_of_shape_of_has_finite_limits
  (J : Type w) [small_category J] [fin_category J] [has_finite_limits_of_size.{w} C] :
  has_limits_of_shape J C := has_finite_limits_of_size.out J

@[priority 100]
instance has_finite_limits_of_has_limits_of_size [has_limits_of_size.{v' u'} C] :
  has_finite_limits_of_size.{w} C :=
⟨λ J hJ hJ', by { haveI := has_limits_of_size_shrink.{0 0} C,
  exact has_limits_of_shape_of_equivalence (fin_category.equiv_as_type J) }⟩

/-- If `C` has all limits, it has finite limits. -/
@[priority 100]
instance has_finite_limits_of_has_limits [has_limits C] : has_finite_limits_of_size.{w} C :=
infer_instance

/-- We can always derive `has_finite_limits_of_size C` for a smaller universe. -/
lemma has_finite_limits_shrink [has_finite_limits_of_size.{(max w w')} C] :
  has_finite_limits_of_size.{w} C :=
⟨λ J _ _, by exactI has_limits_of_shape_of_equivalence
  (ulift_hom_ulift_category.equiv.{w' w' w} J).symm ⟩

/-- We can always derive `has_finite_limits C` if we have `has_finite_limits_of_size.{w} C`
for any universe `w`. -/
lemma has_finite_limits_of_has_finite_limits_of_size [has_finite_limits_of_size.{w} C] :
  has_finite_limits C := has_finite_limits_shrink C

/--
A category has all finite colimits of size `w` if every functor `J ⥤ C` with a `fin_category J`
instance and `J : Type w` has a colimit.

This is often called 'finitely cocomplete'.
-/
class has_finite_colimits_of_size : Prop :=
(out (J : Type w) [𝒥 : small_category J] [@fin_category J 𝒥] : @has_colimits_of_shape J 𝒥 C _)

/-- Most often we will want to use having finite colimits at universe level `0`. We will call this
`has_finite_colimits`. -/
abbreviation has_finite_colimits := has_finite_colimits_of_size.{0}

@[priority 100]
instance has_limits_of_shape_of_has_finite_colimits
  (J : Type w) [small_category J] [fin_category J] [has_finite_colimits_of_size.{w} C] :
  has_colimits_of_shape J C := has_finite_colimits_of_size.out J


@[priority 100]
instance has_finite_colimits_of_has_colimits_of_size [has_colimits_of_size.{v' u'} C] :
  has_finite_colimits_of_size.{w} C :=
⟨λ J hJ hJ', by { haveI := has_colimits_of_size_shrink.{0 0} C,
  exact has_colimits_of_shape_of_equivalence (fin_category.equiv_as_type J) }⟩

/-- If `C` has all colimits, it has finite colimits. -/
@[priority 100]
instance has_finite_colimits_of_has_colimits [has_colimits C] :
  has_finite_colimits_of_size.{w} C :=
infer_instance

/-- We can always derive `has_finite_colimits_of_size C` for a smaller universe. -/
lemma has_finite_colimits_shrink [has_finite_colimits_of_size.{(max w w')} C] :
  has_finite_colimits_of_size.{w} C :=
⟨λ J _ _, by exactI has_colimits_of_shape_of_equivalence
  (ulift_hom_ulift_category.equiv.{w' w' w} J).symm ⟩

/-- We can always derive `has_finite_colimits C` if we have `has_finite_colimits_of_size.{w} C`
for any universe `w`. -/
lemma has_finite_colimits_of_has_finite_colimits_of_size [has_finite_colimits_of_size.{w} C] :
  has_finite_colimits C := has_finite_colimits_shrink C

section

open walking_parallel_pair walking_parallel_pair_hom

instance fintype_walking_parallel_pair : fintype walking_parallel_pair :=
{ elems := [walking_parallel_pair.zero, walking_parallel_pair.one].to_finset,
  complete := λ x, by { cases x; simp } }

local attribute [tidy] tactic.case_bash

instance (j j' : walking_parallel_pair) : fintype (walking_parallel_pair_hom j j') :=
{ elems := walking_parallel_pair.rec_on j
    (walking_parallel_pair.rec_on j' [walking_parallel_pair_hom.id zero].to_finset
      [left, right].to_finset)
    (walking_parallel_pair.rec_on j' ∅ [walking_parallel_pair_hom.id one].to_finset),
  complete := by tidy }

end

instance : fin_category walking_parallel_pair := { }

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
example [has_finite_limits C] : has_equalizers C := by apply_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
example [has_finite_colimits C] : has_coequalizers C := by apply_instance

variables {J : Type v}

local attribute [tidy] tactic.case_bash

namespace wide_pullback_shape

instance fintype_obj [fintype J] : fintype (wide_pullback_shape J) :=
by { rw wide_pullback_shape, apply_instance }

instance fintype_hom (j j' : wide_pullback_shape J) : fintype (j ⟶ j') :=
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

end wide_pullback_shape

namespace wide_pushout_shape

instance fintype_obj [fintype J] : fintype (wide_pushout_shape J) :=
by { rw wide_pushout_shape, apply_instance }

instance fintype_hom (j j' : wide_pushout_shape J) : fintype (j ⟶ j') :=
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

end wide_pushout_shape

instance fin_category_wide_pullback [fintype J] : fin_category (wide_pullback_shape J) :=
{ fintype_hom := wide_pullback_shape.fintype_hom }

instance fin_category_wide_pushout [fintype J] :
  fin_category (wide_pushout_shape J) :=
{ fintype_hom := wide_pushout_shape.fintype_hom }

/--
`has_finite_wide_pullbacks` represents a choice of wide pullback
for every finite collection of morphisms
-/
-- We can't just made this an `abbreviation`
-- because of https://github.com/leanprover-community/lean/issues/429
class has_finite_wide_pullbacks : Prop :=
(out (J : Type w) [fintype J] : has_limits_of_shape (wide_pullback_shape J) C)

instance has_limits_of_shape_wide_pullback_shape
  (J : Type w) [fintype J] [has_finite_wide_pullbacks C] :
  has_limits_of_shape (wide_pullback_shape J) C :=
by { haveI := @has_finite_wide_pullbacks.out C _ _ J, apply_instance }

/--
`has_finite_wide_pushouts` represents a choice of wide pushout
for every finite collection of morphisms
-/
class has_finite_wide_pushouts : Prop :=
(out (J : Type w) [fintype J] : has_colimits_of_shape (wide_pushout_shape J) C)

instance has_colimits_of_shape_wide_pushout_shape
  (J : Type w) [fintype J] [has_finite_wide_pushouts C] :
  has_colimits_of_shape (wide_pushout_shape J) C :=
by { haveI := @has_finite_wide_pushouts.out C _ _ J, apply_instance }

/--
Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
lemma has_finite_wide_pullbacks_of_has_finite_limits [has_finite_limits_of_size.{w} C] :
  has_finite_wide_pullbacks.{w} C :=
⟨λ J _, by exactI has_finite_limits_of_size.out _⟩

/--
Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
lemma has_finite_wide_pushouts_of_has_finite_limits [has_finite_colimits_of_size.{w} C] :
  has_finite_wide_pushouts.{w} C :=
⟨λ J _, by exactI has_finite_colimits_of_size.out _⟩

instance fintype_walking_pair : fintype walking_pair :=
{ elems := {walking_pair.left, walking_pair.right},
  complete := λ x, by { cases x; simp } }

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
example [has_finite_wide_pullbacks.{0} C] : has_pullbacks C := by apply_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
example [has_finite_wide_pushouts.{0} C] : has_pushouts C := by apply_instance

end category_theory.limits
