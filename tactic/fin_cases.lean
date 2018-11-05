/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison

Case bashing on `fin n`, for explicit numerals `n`.
-/
import data.fin

namespace tactic
open lean.parser
open interactive interactive.types expr

meta def fin_cases_at (e : expr) : tactic unit :=
do `(fin %%n) ← infer_type e,
   n ← eval_expr ℕ n,
   [(_, [val, bd], _)] ← cases_core e [`val, `bd],
   -- We now call `cases val` n times, rotating the generated goals out of the way.
   iterate_at_most n (do val ← get_local `val, cases val, rotate 1),
   -- We've got an absurd hypothesis `bd`, but it is messy: it looks like
   -- `nat.succ (... (nat.succ val)) < n`
   -- So we rewrite it as `bd : val + 1 + ... + 1 < n`, and use `dec_trivial` to kill it.
   ss ← mk_const `nat.succ_eq_add_one,
   bd ← get_local `bd,
   (list.range n).mfoldl (λ bd _, do rewrite_hyp ss bd) bd,
   to_expr ``(absurd %%bd dec_trivial) >>= exact,
   -- We put the goals back in order, and clear the `bd` hypotheses.
   iterate_exactly n (do rotate_right 1,
                         try `[rw [fin.mk_val]],
                         try (get_local `bd >>= clear))

namespace interactive
private meta def hyp := tk "*" *> return none <|> some <$> ident

/--
`fin_cases h` performs case analysis on a hypothesis `h : fin n`, where `n` is an explicit natural
number. `fin_cases *` performs case analysis on all suitable hypotheses.

As an example, in
```
example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases p,
  all_goals { assumption }
end
```
after `fin_cases p`, there are three goals, `f 0`, `f 1`, and `f 2`.
-/
meta def fin_cases : parse hyp → tactic unit
| none := do ctx ← local_context,
             ctx.mfirst fin_cases_at <|> fail "No explicit `fin n` hypotheses."
| (some n) := do h ← get_local n, fin_cases_at h
end interactive

end tactic