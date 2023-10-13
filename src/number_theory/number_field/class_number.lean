/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import number_theory.class_number.admissible_abs
import number_theory.class_number.finite
import number_theory.number_field.basic

/-!
# Class numbers of number fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the class number of a number field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `number_field.class_number`: the class number of a number field is the (finite)
cardinality of the class group of its ring of integers
-/

namespace number_field

variables (K : Type*) [field K] [number_field K]

namespace ring_of_integers

noncomputable instance : fintype (class_group (ring_of_integers K)) :=
class_group.fintype_of_admissible_of_finite ℚ K absolute_value.abs_is_admissible

end ring_of_integers

/-- The class number of a number field is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ := fintype.card (class_group (ring_of_integers K))

variables {K}

/-- The class number of a number field is `1` iff the ring of integers is a PID. -/
theorem class_number_eq_one_iff :
  class_number K = 1 ↔ is_principal_ideal_ring (ring_of_integers K) :=
card_class_group_eq_one_iff

end number_field

namespace rat

open number_field

theorem class_number_eq : number_field.class_number ℚ = 1 :=
class_number_eq_one_iff.mpr $ by convert is_principal_ideal_ring.of_surjective
  (rat.ring_of_integers_equiv.symm : ℤ →+* ring_of_integers ℚ)
  (rat.ring_of_integers_equiv.symm.surjective)

end rat
