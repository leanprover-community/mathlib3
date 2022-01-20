/-
Copyright (c) 2021 Johan Commelin.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Kevin Buzzard
-/
import algebra.order.monoid

/-!
An example of a `linear_ordered_comm_monoid_with_zero` in which the product of two positive
elements vanishes.

This is the monoid with 3 elements `0, ε, 1` where `ε ^ 2 = 0` and everything else is forced.
The order is `0 < ε < 1`.  Since `ε ^ 2 = 0`, the product of strictly positive elements can vanish.

Relevant Zulip chat:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/mul_pos
-/

/--  The three element monoid. -/
@[derive [decidable_eq]]
inductive foo
| zero
| eps
| one


namespace foo

instance inhabited : inhabited foo := ⟨zero⟩

instance : has_zero foo := ⟨zero⟩
instance : has_one foo := ⟨one⟩
notation `ε` := eps

/-- The order on `foo` is the one induced by the natural order on the image of `aux1`. -/
def aux1 : foo → ℕ
| 0 := 0
| ε := 1
| 1 := 2

/-- A tactic to prove facts by cases. -/
meta def boom : tactic unit :=
`[repeat {rintro ⟨⟩}; dec_trivial]

lemma aux1_inj : function.injective aux1 :=
by boom

instance : linear_order foo :=
linear_order.lift aux1 $ aux1_inj

/-- Multiplication on `foo`: the only external input is that `ε ^ 2 = 0`. -/
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
  zero_le_one := dec_trivial,
  .. foo.linear_order,
  .. foo.comm_monoid }

lemma not_mul_pos : ¬ ∀ {M : Type} [linear_ordered_comm_monoid_with_zero M], by exactI ∀
  (a b : M) (ha : 0 < a) (hb : 0 < b),
  0 < a * b :=
begin
  intros h,
  specialize h ε ε (by boom) (by boom),
  exact (lt_irrefl 0 (h.trans_le (by boom))).elim,
end

example : 0 < ε ∧ ε * ε = 0 := by boom

end foo
