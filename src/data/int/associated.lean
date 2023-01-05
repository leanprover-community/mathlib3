/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import algebra.associated
import data.int.units

/-!
# Associated elements and the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results on equality up to units in the integers.

## Main results

 * `int.nat_abs_eq_iff_associated`: the absolute value is equal iff integers are associated
-/

lemma int.nat_abs_eq_iff_associated {a b : ℤ} :
  a.nat_abs = b.nat_abs ↔ associated a b :=
begin
  refine int.nat_abs_eq_nat_abs_iff.trans _,
  split,
  { rintro (rfl | rfl),
    { refl },
    { exact ⟨-1, by simp⟩ } },
  { rintro ⟨u, rfl⟩,
    obtain (rfl | rfl) := int.units_eq_one_or u,
    { exact or.inl (by simp) },
    { exact or.inr (by simp) } }
end
