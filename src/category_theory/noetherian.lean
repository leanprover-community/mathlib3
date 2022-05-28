/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.subobject.lattice
import category_theory.essentially_small
import category_theory.simple

/-!
# Artinian and noetherian categories

An artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.

A noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.

We show that any nonzero artinian object has a simple subobject.

## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.
-/

namespace category_theory
open category_theory.limits

variables {C : Type*} [category C]

/--
A noetherian object is an object
which does not have infinite increasing sequences of subobjects.

See https://stacks.math.columbia.edu/tag/0FCG
-/
class noetherian_object (X : C) : Prop :=
(subobject_gt_well_founded : well_founded ((>) : subobject X → subobject X → Prop))

/--
An artinian object is an object
which does not have infinite decreasing sequences of subobjects.

See https://stacks.math.columbia.edu/tag/0FCF
-/
class artinian_object (X : C) : Prop :=
(subobject_lt_well_founded [] : well_founded ((<) : subobject X → subobject X → Prop))

variables (C)

/-- A category is noetherian if it is essentially small and all objects are noetherian. -/
class noetherian extends essentially_small C :=
(noetherian_object : ∀ (X : C), noetherian_object X)

attribute [priority 100, instance] noetherian.noetherian_object

/-- A category is artinian if it is essentially small and all objects are artinian. -/
class artinian extends essentially_small C :=
(artinian_object : ∀ (X : C), artinian_object X)

attribute [priority 100, instance] artinian.artinian_object

variables {C}

open subobject
variables [has_zero_morphisms C] [has_zero_object C]

lemma exists_simple_subobject {X : C} [artinian_object X] (h : ¬ is_zero X) :
  ∃ (Y : subobject X), simple (Y : C) :=
begin
  haveI : nontrivial (subobject X) := nontrivial_of_not_is_zero h,
  haveI := is_atomic_of_order_bot_well_founded_lt (artinian_object.subobject_lt_well_founded X),
  have := is_atomic.eq_bot_or_exists_atom_le (⊤ : subobject X),
  obtain ⟨Y, s⟩ := (is_atomic.eq_bot_or_exists_atom_le (⊤ : subobject X)).resolve_left top_ne_bot,
  exact ⟨Y, (subobject_simple_iff_is_atom _).mpr s.1⟩,
end

/-- Choose an arbitrary simple subobject of a non-zero artinian object. -/
noncomputable def simple_subobject {X : C} [artinian_object X] (h : ¬ is_zero X) : C :=
(exists_simple_subobject h).some

/-- The monomorphism from the arbitrary simple subobject of a non-zero artinian object. -/
@[derive mono]
noncomputable def simple_subobject_arrow {X : C} [artinian_object X] (h : ¬ is_zero X) :
  simple_subobject h ⟶ X :=
(exists_simple_subobject h).some.arrow

instance {X : C} [artinian_object X] (h : ¬ is_zero X) : simple (simple_subobject h) :=
(exists_simple_subobject h).some_spec

end category_theory
