/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.core
import tactic.calc_step.lemmas

namespace tactic

open calc_step calc_step.side calc_step.op calc_step.sign

/-- The default side that the `calc_step` tactic acts on is on the left,
but for `div` (division) the default is to divide on the right. -/
meta def get_side : option side → op → sign → side
| (some s) _   _ := s
| none     div _ := R
| _        _   _ := L

meta def calc_step_aux (e : pexpr) (n : name) : tactic unit :=
_

meta def calc_step (e : pexpr) (s : option side) (op : op) (sgn : sign) : tactic unit :=
focus1 $
do ctx ← local_context,
  let sd := get_side s op sgn,
  let lems := lookup.find (sd, op, sgn),
  lems.mfirst (calc_step_aux e)
  --
  -- n ← get_unused_name `nonzero,
  -- to_expr ``(%%e ≠ 0) >>= assert n,
  -- focus1 `[try { assumption <|> norm_num, done }],
  -- swap,
  -- h0 ← get_local n,
  -- match s with
  -- | (some side.R) := `[apply (mul_left_inj' %%h0).mp]
  -- | _             := `[apply (mul_right_inj' %%h0).mp]
  -- end,
  -- clear h0

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

meta def side_p : lean.parser calc_step.side :=
do t <- ident, if t = `L then return side.L else if t = `R then return side.R else failed

meta def add_by (q : parse parser.pexpr) (s : parse side_p?) : tactic unit :=
tactic.add_by q s

meta def mul_by (q : parse parser.pexpr) (s : parse side_p?) : tactic unit :=
tactic.mul_by q s

meta def dummy (q : parse parser.pexpr) (s : parse side_p?) : tactic unit :=
tactic.calc_step q s mul none

end interactive

end tactic

example (a b : ℕ) (ha : a ≠ 0) (h : 2 * a = 2 * b) : a = b :=
begin
  dummy a L,
  -- mul_by a L,
end

example (a b : ℂ) (x : ℂ) (h : x * a = x * b) : a = b :=
begin
  mul_by (2:ℂ),
end
