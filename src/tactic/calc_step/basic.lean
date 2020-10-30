/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.core
import tactic.calc_step.lemmas
import tactic.norm_num

#print tactic.to_expr

meta def expr.elab (e : pexpr) (allow_mvars : opt_param bool tt) (subgoals : opt_param bool tt) :
  tactic expr :=
tactic.to_expr e allow_mvars subgoals

namespace tactic

open calc_step calc_step.side calc_step.op calc_step.sign

-- move this to `calc_step` namespace
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

-- meta def analyze_type : expr → option (ℕ × list ℕ)
-- | `(%%lhs ↔ %%rhs) := _
-- | `(%%lhs = %%rhs) := _
-- | `(%%lhs ≤ %%rhs) := _
-- | `(%%lhs < %%rhs) := _
-- | `(%%lhs ≠ %%rhs) := _
-- | _ := none


-- meta def find_named_arg (n : name) : expr → option ℕ
-- | (expr.pi a _ _ e) := if n = a then some 0 else nat.succ <$> find_named_arg e
-- | _ := none

-- meta def apply_named_arg (d : declaration) (n : name) (v : expr) : tactic expr :=
-- do e ← resolve_name d.to_name,
--   match find_named_arg n d.type with
--   | none := failed
--   | some n := _
--   end

-- run_cmd do
--   d ← get_decl ``has_add.add,
--   n ← find_named_arg `c d.type,
--   trace n -- 1

meta def calc_step_unary (n : name) : tactic expr :=
failed -- fix this

meta def calc_step_binary (e : pexpr) (goal : expr) (pat : expr → expr → pexpr) : tactic expr :=
do e' ← e.elab,
  t ← target, r ← (``(%%(pat e' goal) : %%t)).elab, return r

meta def calc_step (e : option pexpr) (s : side) (op : op) (sgn : sign) : tactic unit :=
focus1 $ do
  let sd := get_side s op,
  newgoal ← mk_mvar,
  prf ← match e with
  | none := (lookup.find (sd, op, sgn)).mfirst calc_step_unary
  | some x := (lookup_binary.find (sd, op, sgn)).mfirst (calc_step_binary x newgoal)
  end,
  apply prf,
  all_goals' $ try $ `[assumption <|> norm_num, done],
  gs ← get_goals,
  set_goals (newgoal::gs)

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

example (a b : ℚ) (x : ℚ) (h : 2 * a < 2 * b) : a < b :=
begin
  -- negate,
  -- take_inv neg,
  mul_by 2 L pos,
  assumption,
end
