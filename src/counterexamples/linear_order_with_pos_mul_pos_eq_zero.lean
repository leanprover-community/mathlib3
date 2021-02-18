/-
Copyright (c) 2021 Johan Commelin (inspired by Kevin Buzzard, copied by Damiano Testa).
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin (inspired by Kevin Buzzard, copied by Damiano Testa)
-/
import algebra.ordered_monoid

/-!
An example of a `linear_ordered_comm_monoid_with_zero` in which the product of two positive
elements vanishes.

This is the monoid with 3 elements `0, ε, 1` where `ε ^ 2 = 0` and everything else is forced.
The order is `0 < ε < 1`.  Since `ε ^ 2 = 0`, the product of strictly positive elements can vanish.

Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/mul_pos
-/

@[derive [decidable_eq]]
inductive foo
| zero
| eps
| one

namespace foo

instance : has_zero foo := ⟨zero⟩
instance : has_one foo := ⟨one⟩
notation `ε` := eps

def aux1 : foo → ℕ
| 0 := 0
| ε := 1
| 1 := 2

meta def boom : tactic unit :=
`[repeat {rintro ⟨⟩}; dec_trivial]

lemma aux1_inj : function.injective aux1 :=
by boom

instance : linear_order foo :=
linear_order.lift aux1 $ aux1_inj

def mul : foo → foo → foo
| 1 x := x
| x 1 := x
| _ _ := 0

instance : comm_monoid foo :=
{ mul := mul,
  one := 1,
  one_mul := by boom,
  mul_one := by boom,
  mul_comm := by boom,
  mul_assoc := by boom }

instance : linear_ordered_comm_monoid_with_zero foo :=
{ zero := 0,
  zero_mul := by boom,
  mul_zero := by boom,
  mul_le_mul_left := by { rintro ⟨⟩ ⟨⟩ h ⟨⟩; revert h; dec_trivial },
  lt_of_mul_lt_mul_left := by { rintro ⟨⟩ ⟨⟩ ⟨⟩; dec_trivial },
  zero_le_one := dec_trivial,
  .. foo.linear_order,
  .. foo.comm_monoid }

example : 0 < ε ∧ ε * ε = 0 := by boom

end foo
