/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing on `fin n`, for explicit numerals `n`.
-/
import tactic.linarith

namespace tactic

meta def fin_cases_at (e : expr) : tactic unit :=
do `(fin %%n) ← infer_type e,
   guard n.is_numeral,
   [(_, [val, bd], _)] ← cases_core e [`val, `bd],
   n ← eval_expr ℕ n,
   -- We now call `cases val` n times, rotating the generated goals out of the way.
   iterate_at_most n (do val ← get_local `val, cases val, rotate 1),
   -- We've got an absurd hypothesis, but it is messy: it looks like
   -- `nat.succ (... (nat.succ val)) < n`
   -- So we rewrite it as `val + 1 + ... + 1 < n`, and call `linarith` to kill it.
   ss ← mk_const `nat.succ_eq_add_one,
   bd ← get_local `bd,
   (list.range n).mfoldl (λ bd _, do rewrite_hyp ss bd) bd,
   exfalso >> `[linarith],
   -- Finally we put the goals back in order.
   rotate_right n

meta def fin_cases : tactic unit :=
do ctx ← local_context,
   ctx.mfirst fin_cases_at <|> fail "No explicit `fin n` hypotheses."

run_cmd add_interactive [`fin_cases]

-- TODO would it be valuable to have an interactive tactic with a parser, so we can aim this
-- at individual hypotheses, rather than just the first that matches?
end tactic