/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import number_theory.class_number.admissible_card_pow_degree
import number_theory.class_number.finite
import number_theory.function_field

/-!
# Class numbers of function fields

This file defines the class number of a function field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `function_field.class_number`: the class number of a function field is the (finite)
cardinality of the class group of its ring of integers
-/

namespace function_field

variables (Fq F : Type) [field Fq] [fintype Fq] [field F]
variables [algebra (polynomial Fq) F] [algebra (fraction_ring (polynomial Fq)) F]
variables [is_scalar_tower (polynomial Fq) (fraction_ring (polynomial Fq)) F]
variables [function_field Fq F] [is_separable (fraction_ring (polynomial Fq)) F]

open_locale classical

namespace ring_of_integers

open function_field

noncomputable instance  : fintype (class_group (ring_of_integers Fq F) F) :=
class_group.fintype_of_admissible_of_finite (fraction_ring (polynomial Fq)) F
  (polynomial.card_pow_degree_is_admissible : absolute_value.is_admissible
    (polynomial.card_pow_degree : absolute_value (polynomial Fq) ℤ))

end ring_of_integers

/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def class_number : ℕ := fintype.card (class_group (ring_of_integers Fq F) F)

/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
theorem class_number_eq_one_iff :
  class_number Fq F = 1 ↔ is_principal_ideal_ring (ring_of_integers Fq F) :=
card_class_group_eq_one_iff

end function_field
