/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.cast.lemmas
import data.nat.cast.prod

/-!
# The product of two `add_group_with_one`s.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace prod

variables {α β : Type*} [add_group_with_one α] [add_group_with_one β]

instance : add_group_with_one (α × β) :=
{ int_cast := λ n, (n, n),
  int_cast_of_nat := λ _, by simp; refl,
  int_cast_neg_succ_of_nat := λ _, by simp; refl,
  .. prod.add_monoid_with_one, .. prod.add_group }

@[simp] lemma fst_int_cast (n : ℤ) : (n : α × β).fst = n := rfl

@[simp] lemma snd_int_cast (n : ℤ) : (n : α × β).snd = n := rfl

end prod
