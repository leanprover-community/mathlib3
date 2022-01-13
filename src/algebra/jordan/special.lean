/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.symmetrized
import algebra.jordan.basic

/-!
# Special Jordan algebras

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrisation" i.e
```
a∘b = 1/2(ab+ba).
```
When the original multiplication is associative, the symmetrised algebra is a commutative Jordan
algebra. A commutative Jordan algebra which can be constructed in this way from an associative
multiplication is said to be a special Jordan algebra.

## Main results

- `is_comm_jordan` : The symmeterised algebra arising from an associative algebra is a commutative
  Jordan algebra.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/


open sym_alg

/- 2 commutes with every element of a ring -/
lemma two_commute {α : Type*} [ring α] (a : α) : commute 2 a := begin
  --convert commute.semiconj_by 2 a,
  unfold _root_.commute,
  rw [semiconj_by, mul_two, two_mul],
end

/- If 2 is invertible, ⅟2 commutes with every element of a ring -/
lemma half_commute {α : Type*} [ring α] [invertible (2 : α)] (a : α) : commute (⅟2) a :=
  commute.inv_of_left (two_commute a)

/- The symmetrisation of a real (unital, associative) algebra multiplication is a commutative
Jordan non-associative ring -/
instance (α : Type*) [ring α] [invertible (2 : α)] : is_comm_jordan (αˢʸᵐ) :=
{ mul_comm := λ a,
  begin
    intro,
    change ⅟2 * (unsym a * unsym b + unsym b * unsym a) =
      ⅟2 * (unsym b * unsym a + unsym a * unsym b),
    rw add_comm,
  end,
  jordan := λ a,
  begin
    intro,
    change ⅟2 * (⅟2 * (unsym a * unsym b + unsym b * unsym a) * unsym(a*a)
      + unsym(a*a) * (⅟2 * (unsym a * unsym b + unsym b * unsym a)))
      = ⅟2 * (unsym a * (⅟2 * (unsym b * unsym(a*a) + unsym(a*a) * unsym b))
        + (⅟2 * (unsym b * unsym(a*a) + unsym(a*a) * unsym b)) * unsym a),
    -- Rearrange LHS
    rw [← mul_assoc, ← commute.eq (half_commute (unsym (a*a))), mul_assoc, mul_assoc, ← mul_add,
      ← mul_assoc, add_mul, mul_add (unsym (a * a)), ← add_assoc, ← mul_assoc, ← mul_assoc],
    -- Rearrange RHS
    rw [← mul_assoc, ← commute.eq (half_commute (unsym a)), mul_assoc (⅟2) (unsym a),
      mul_assoc (⅟2) _ (unsym a), ← mul_add, ← mul_assoc],
    nth_rewrite_rhs 0 mul_add (unsym a),
    rw [add_mul, ← add_assoc, ← mul_assoc, ← mul_assoc],

    rw unsym_mul_self,
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_eq_zero, ← mul_sub],

    convert mul_zero (⅟(2:α) * ⅟(2:α)),
    rw [add_sub_add_right_eq_sub, add_assoc, add_assoc, add_sub_add_left_eq_sub, add_comm,
      add_sub_add_right_eq_sub, sub_eq_zero],
  end }
