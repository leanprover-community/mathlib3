/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.field.basic
import algebra.ring.ulift

/-!
# Field instances for `ulift`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for field, semifield and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)
-/

universes u v
variables {α : Type u} {x y : ulift.{v} α}

namespace ulift

instance [has_rat_cast α] : has_rat_cast (ulift α) := ⟨λ a, up a⟩

@[simp, norm_cast] lemma up_rat_cast [has_rat_cast α] (q : ℚ) : up (q : α) = q := rfl
@[simp, norm_cast] lemma down_rat_cast [has_rat_cast α] (q : ℚ) : down (q : ulift α) = q := rfl

instance division_semiring [division_semiring α] : division_semiring (ulift α) :=
by refine down_injective.division_semiring down _ _ _ _ _ _ _ _ _ _; intros; refl

instance semifield [semifield α] : semifield (ulift α) :=
{ ..ulift.division_semiring, ..ulift.comm_group_with_zero }

instance division_ring [division_ring α] : division_ring (ulift α) :=
{ ..ulift.division_semiring, ..ulift.add_group }

instance field [field α] : field (ulift α) :=
{ ..ulift.semifield, ..ulift.division_ring }

end ulift
