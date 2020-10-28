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
meta def get_side : side → op → side
| L _   := L
| R _   := R
| N mul := L
| N add := L
| N div := R
| N sub := R
| _ _   := N

meta def calc_step_unary (n : name) : tactic unit :=
do lem ← resolve_name n, tactic.interactive.refine ``(%%lem _)

meta def calc_step_binary (e : pexpr) (n : name) : tactic unit :=
do lem ← resolve_name n, tactic.interactive.refine ``(%%lem %%e _)

meta def calc_step (e : option pexpr) (s : side) (op : op) (sgn : sign) : tactic unit :=
focus1 $ do
  let sd := get_side s op,
  let lems := lookup.find (sd, op, sgn),
  match e with
  | none := lems.mfirst calc_step_unary
  | some x := lems.mfirst (calc_step_binary x)
  end,
  gs ← get_goals,
  match gs with
  | (h::t) := do
    set_goals t,
    all_goals' $ try $ `[assumption <|> norm_num, done],
    gs ← get_goals,
    set_goals (h::gs)
  | _ := skip
  end

namespace interactive

setup_tactic_parser

meta def side_p : lean.parser calc_step.side :=
do t ← ident, if t = `L then return side.L else if t = `R then return side.R else failed

meta def sign_p : lean.parser calc_step.sign :=
do t ← ident,
if t = `pos then return sign.pos else
if t = `neg then return sign.neg else
                 return sign.none

meta def add (q : parse parser.pexpr) (s : parse side_p?) : tactic unit :=
tactic.calc_step q s.iget op.add none

meta def negate : tactic unit :=
tactic.calc_step none N neg none

meta def subtract (q : parse parser.pexpr) (s : parse side_p?) : tactic unit :=
tactic.calc_step q s.iget sub none

meta def mul_by (q : parse parser.pexpr) (s : parse side_p?) (sgn : parse sign_p?) : tactic unit :=
tactic.calc_step q s.iget mul sgn.iget

meta def div_by (q : parse parser.pexpr) (s : parse side_p?) (sgn : parse sign_p?) : tactic unit :=
tactic.calc_step q s.iget div sgn.iget

meta def take_inv (sgn : parse sign_p?) : tactic unit :=
tactic.calc_step none N inv sgn.iget

end interactive

end tactic

example (a b : ℕ) (ha : a ≠ 0) (h : 2 * a = 2 * b) : a = b :=
begin
  mul_by 2,
end

example (a b : ℝ) (x : ℝ) (h : 2 * a < 2 * b) : a < b :=
begin
  -- negate,
  -- take_inv pos,
  mul_by 2 L pos,
end
