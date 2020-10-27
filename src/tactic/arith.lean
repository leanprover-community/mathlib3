/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.core

-- imports for tests
import algebra.group_with_zero
import ring_theory.witt_vector.basic
import analysis.special_functions.trigonometric

open lean.parser

/-

## Without order

### mul
left_cancel_semigroup     `mul_right_inj`
right_cancel_semigroup    `mul_left_inj`
cancel_monoid_with_zero   `mul_left_inj'`  `mul_right_inj'`

### add
left_cancel_add_semigroup    `add_right_inj`
right_cancel_add_semigroup   `add_left_inj`

### sub
add_group          `sub_left_inj`   `sub_right_inj`

### neg
add_group          `neg_inj`

### inv
group                   `inv_inj`
group_with_zero         `inv_inj'`

## With order

ordered_cancel_comm_monoid `mul_le_mul_iff_left`   `mul_le_mul_iff_right`

linear_ordered_semiring `mul_le_mul_left`    `mul_le_mul_right`

linear_ordered_ring      `mul_le_mul_left_of_neg`    `mul_le_mul_right_of_neg`

-/

namespace arith

inductive rel : Type
| eq
| ne -- can we pull this off?
| le
| lt

@[derive [decidable_eq, has_reflect, inhabited]]
inductive side | L | R

meta instance : has_to_format side :=
⟨ λ x, match x with
| side.L := "L"
| side.R := "R"
end ⟩

end arith

namespace tactic

open arith

meta def add_by (e : pexpr) : option side → tactic unit
| (some side.R) := do `[apply (add_right_inj %%e).mp]
| _ := do `[apply (add_right_inj %%e).mp]

meta def mul_by (e : pexpr) (s : option side) : tactic unit :=
focus1 $
do ctx ← local_context,
  n ← get_unused_name `nonzero,
  to_expr ``(%%e ≠ 0) >>= assert n,
  focus1 `[try { assumption <|> norm_num, done }],
  swap,
  h0 ← get_local n,
  match s with
  | (some side.R) := `[apply (mul_left_inj' %%h0).mp]
  | _             := `[apply (mul_right_inj' %%h0).mp]
  end,
  clear h0

namespace interactive

setup_tactic_parser

meta def side_p : lean.parser arith.side :=
do t <- ident, if t = `L then return side.L else if t = `R then return side.R else failed

meta def add_by (q : parse parser.pexpr) (s : parse side_p?) : tactic unit :=
tactic.add_by q s

meta def mul_by (q : parse parser.pexpr) (s : parse side_p?) : tactic unit :=
tactic.mul_by q s

end interactive

end tactic

example (a b : ℕ) (ha : a ≠ 0) (h : 2 * a = 2 * b) : a = b :=
begin
  mul_by a L,
end

example (a b : ℂ) (x : ℂ) (h : x * a = x * b) : a = b :=
begin
  mul_by (2:ℂ),
end
