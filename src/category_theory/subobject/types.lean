/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.subobject.well_powered
import category_theory.types

/-!
# `Type u` is well-powered

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

By building a categorical equivalence `mono_over α ≌ set α` for any `α : Type u`,
we deduce that `subobject α ≃o set α` and that `Type u` is well-powered.

One would hope that for a particular concrete category `C` (`AddCommGroup`, etc)
it's viable to prove `[well_powered C]` without explicitly aligning `subobject X`
with the "hand-rolled" definition of subobjects.

This may be possible using Lawvere theories,
but it remains to be seen whether this just pushes lumps around in the carpet.
-/

universes u

open category_theory
open category_theory.subobject

open_locale category_theory.Type

lemma subtype_val_mono {α : Type u} (s : set α) : mono ↾(subtype.val : s → α) :=
(mono_iff_injective _).mpr subtype.val_injective

local attribute [instance] subtype_val_mono

/--
The category of `mono_over α`, for `α : Type u`, is equivalent to the partial order `set α`.
-/
@[simps]
noncomputable
def types.mono_over_equivalence_set (α : Type u) : mono_over α ≌ set α :=
{ functor :=
  { obj := λ f, set.range f.1.hom,
    map := λ f g t, hom_of_le begin
      rintro a ⟨x, rfl⟩,
      exact ⟨t.1 x, congr_fun t.w x⟩,
    end, },
  inverse :=
  { obj := λ s, mono_over.mk' (subtype.val : s → α),
    map := λ s t b, mono_over.hom_mk (λ w, ⟨w.1, set.mem_of_mem_of_subset w.2 b.le⟩)
      (by { ext, simp, }), },
  unit_iso := nat_iso.of_components
    (λ f, mono_over.iso_mk
      (equiv.of_injective f.1.hom ((mono_iff_injective _).mp f.2)).to_iso (by tidy))
    (by tidy),
  counit_iso := nat_iso.of_components
    (λ s, eq_to_iso subtype.range_val)
    (by tidy), }

instance : well_powered (Type u) :=
well_powered_of_essentially_small_mono_over
  (λ α, essentially_small.mk' (types.mono_over_equivalence_set α))

/--
For `α : Type u`, `subobject α` is order isomorphic to `set α`.
-/
noncomputable def types.subobject_equiv_set (α : Type u) : subobject α ≃o set α :=
(types.mono_over_equivalence_set α).thin_skeleton_order_iso
