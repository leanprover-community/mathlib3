/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.cast.basic
import algebra.group.prod

/-!
# The product of two `add_monoid_with_one`s.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α β : Type*}

namespace prod
variables [add_monoid_with_one α] [add_monoid_with_one β]

instance : add_monoid_with_one (α × β) :=
{ nat_cast := λ n, (n, n),
  nat_cast_zero := congr_arg2 prod.mk nat.cast_zero nat.cast_zero,
  nat_cast_succ := λ n, congr_arg2 prod.mk (nat.cast_succ _) (nat.cast_succ _),
  .. prod.add_monoid, .. prod.has_one }

@[simp] lemma fst_nat_cast (n : ℕ) : (n : α × β).fst = n :=
by induction n; simp *

@[simp] lemma snd_nat_cast (n : ℕ) : (n : α × β).snd = n :=
by induction n; simp *

end prod
