/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import group_theory.congruence
import algebra.ring.inj_surj

/-!
# Congruence relations on rings

This file defines congruence relations on rings, which extend `con` and `add_con` on monoids and
additive monoids.

Most of the time you likely want to use the `ideal.quotient` API that is built on top of this.

TODO: use this for `ring_quot` too.
-/


/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
structure ring_con (R : Type*) [has_add R] [has_mul R] extends setoid R :=
(add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z))
(mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z))

variables {R : Type*}

namespace ring_con

section basic
variables [has_add R] [has_mul R] (c : ring_con R)

/-- Every `ring_con` is also an `add_con` -/
def to_add_con : add_con R := { ..c }

/-- Every `ring_con` is also a `con` -/
def to_con : con R := { ..c }

/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
protected def quotient := quotient $ c.to_setoid

instance : has_add c.quotient := c.to_add_con.has_add
instance : has_mul c.quotient := c.to_con.has_mul

end basic

section data

instance [add_zero_class R] [has_mul R] (c : ring_con R) :
  has_zero c.quotient := c.to_add_con^.quotient.has_zero
instance [has_add R] [mul_one_class R] (c : ring_con R) :
  has_one c.quotient := c.to_con^.quotient.has_one
instance [add_group R] [has_mul R] (c : ring_con R) :
  has_neg c.quotient := c.to_add_con^.has_neg
instance [add_group R] [has_mul R] (c : ring_con R) :
  has_sub c.quotient := c.to_add_con^.has_sub
instance has_nsmul [add_monoid R] [has_mul R] (c : ring_con R) :
  has_smul ℕ c.quotient := c.to_add_con^.quotient.has_nsmul
instance has_zsmul [add_group R] [has_mul R] (c : ring_con R) :
  has_smul ℤ c.quotient := c.to_add_con^.quotient.has_zsmul
instance [has_add R] [monoid R] (c : ring_con R) :
  has_pow c.quotient ℕ := c.to_con^.nat.has_pow

instance [add_monoid_with_one R] [has_mul R] (c : ring_con R) : has_nat_cast c.quotient :=
⟨λ n, quotient.mk' n⟩
instance [add_group_with_one R] [has_mul R] (c : ring_con R) : has_int_cast c.quotient :=
⟨λ n, quotient.mk' n⟩

end data

section algebraic

instance [non_unital_non_assoc_semiring R] (c : ring_con R) :
  non_unital_non_assoc_semiring c.quotient :=
function.surjective.non_unital_non_assoc_semiring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [non_assoc_semiring R] (c : ring_con R) :
  non_assoc_semiring c.quotient :=
function.surjective.non_assoc_semiring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance [non_unital_semiring R] (c : ring_con R) :
  non_unital_semiring c.quotient :=
function.surjective.non_unital_semiring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [semiring R] (c : ring_con R) :
  semiring c.quotient :=
function.surjective.semiring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance [comm_semiring R] (c : ring_con R) :
  comm_semiring c.quotient :=
function.surjective.comm_semiring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance [non_unital_non_assoc_ring R] (c : ring_con R) :
  non_unital_non_assoc_ring c.quotient :=
function.surjective.non_unital_non_assoc_ring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [non_assoc_ring R] (c : ring_con R) :
  non_assoc_ring c.quotient :=
function.surjective.non_assoc_ring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)
  (λ _, rfl)

instance [non_unital_ring R] (c : ring_con R) :
  non_unital_ring c.quotient :=
function.surjective.non_unital_ring _ quotient.surjective_quotient_mk'
  rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

instance [ring R] (c : ring_con R) :
  ring c.quotient :=
function.surjective.ring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _, rfl) (λ _, rfl)

instance [comm_ring R] (c : ring_con R) :
  comm_ring c.quotient :=
function.surjective.comm_ring _ quotient.surjective_quotient_mk'
  rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _, rfl) (λ _, rfl)

end algebraic

end ring_con
