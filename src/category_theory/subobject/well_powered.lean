/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.subobject.basic
import category_theory.essentially_small

/-!
# Well powered categories

A category `(C : Type u) [category.{v} C]` is `[well_powered C]` if
for every `X : C`, we have `small.{v} (subobject X)`.

(Note that in this situtation `subobject X : Type (max u v)`,
so this is a nontrivial condition for large categories,
but automatic for small categories.)

This is equivalent to the category `mono_over X` being `essentially_small.{v}` for all `X : C`.

When a category is well-powered, you can obtain nonconstructive witnesses as
`shrink (subobject X) : Type v`
and
`equiv_shrink (subobject X) : subobject X ≃ shrink (subobject X)`.
-/

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

/--
A category (with morphisms in `Type v`) is well-powered if `subobject X` is `v`-small for every `X`.

We show in `well_powered_of_mono_over_essentially_small` and `mono_over_essentially_small`
that this is the case if and only if `mono_over X` is `v`-essentially small for every `X`.
-/
class well_powered : Prop :=
(subobject_small : ∀ X : C, small.{v} (subobject X))

instance small_subobject [well_powered C] (X : C) : small.{v} (subobject X) :=
well_powered.subobject_small X

@[priority 100]
instance well_powered_of_small_category (C : Type u) [small_category C] : well_powered C :=
{ subobject_small := λ X, small_self _, }

theorem essentially_small_mono_over_iff_small_subobject {C : Type u} [category.{v} C] (X : C) :
  essentially_small.{v} (mono_over X) ↔ small.{v} (subobject X) :=
begin
  rw essentially_small_iff_of_thin (mono_over.is_thin),
  exact iff.rfl,
end

theorem well_powered_of_mono_over_essentially_small
  (h : ∀ X : C, essentially_small.{v} (mono_over X)) :
  well_powered C :=
{ subobject_small := λ X, (essentially_small_mono_over_iff_small_subobject X).mp (h X), }

variables {C} [well_powered C]

theorem mono_over_essentially_small (X : C) :
  essentially_small.{v} (mono_over X) :=
(essentially_small_mono_over_iff_small_subobject X).mpr (well_powered.subobject_small X)

end category_theory
