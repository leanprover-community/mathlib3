/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.linarith

/-!
# `remove_subs` -- a tactic for splitting nat-subtractions

The tactic `remove_subs` looks for nat-subtractions in the goal and it recursively replaces
any subexpression of the form `a - b` by two branches: one where `a ≤ b` and `a - b` is replaced
by `0` and one where `b < a` and it tries to replace `a` by `b + c`, for some `c : ℕ`.

If `remove_subs` is called with the optional flag `!`, then, after the case splits, the tactic
also tries `linarith` on all remaining goals.
-/

lemma nat.le_cases (a b : ℕ) : a - b = 0 ∨ ∃ c, a = b + c :=
begin
  by_cases ab : a ≤ b,
  { exact or.inl (tsub_eq_zero_of_le ab) },
  { refine or.inr _,
    rcases nat.exists_eq_add_of_le ((not_le.mp ab).le) with ⟨c, rfl⟩,
    exact ⟨_, rfl⟩ },
end

namespace tactic

/--  `get_sub e` extracts a list of pairs `(a, b)` from the expression `e`, where `a - b` is a
subexpression of `e`. -/
meta def get_sub : expr → tactic (list (expr × expr))
| `(%%a - %%b) := do [ga, gb] ← [a, b].mmap get_sub,
                    return ((a, b) :: (ga ++ gb))
| (expr.app f a) := do [gf, ga] ← [f, a].mmap get_sub,
                    return (gf ++ ga)
| _ := pure []

/--  `remove_one_sub a b` assumes that the expression `a - b` occurs in the target.
It splits two cases:
*  `a ≤ b`, in which case it replaces `a - b` with `0`, introduces the inequality `a ≤ b` into
   the local context and tries `simp`;
*  writes `a = b + c`, for some `c`, tries to substitute this equality and tries `simp`.
-/
meta def remove_one_sub (a b : expr) : tactic unit := do
-- introduce names with the following meanings:
-- `eq0 : a - b = 0`, `exis : ∃ c, a = b + c`, `var = c`, `ide : a = b + c`
[eq0, exis, var, ide] ← ["h", "k", "x", "hx"].mmap (λ y, get_unused_name y),
-- either `a ≤ b` or `a = b + c`
cases `(nat.le_cases %%a %%b) [eq0, exis],
-- on the branch where `a ≤ b`...
  prf0 ← get_local eq0,
  rewrite_target prf0,
  to_expr ``(nat.sub_eq_zero_iff_le) >>= λ x, rewrite_hyp x prf0,
swap,
-- on the branch where `b < a`...
  get_local exis >>= λ x, cases x [var, ide],
  -- either substitute or rewrite
  get_local ide >>= (λ x, subst x <|> rewrite_target x),
  vare ← get_local var,
  to_expr ``(nat.add_sub_cancel_left %%b %%vare) >>= rewrite_target <|>
    fail"could not rewrite: something went wrong",
swap

namespace interactive
setup_tactic_parser

/--  Iterate replacing a subtraction with two cases, depending on whether the subtraction is
truncated to `0` or it is an "actual" subtraction.

If an optional `!` is passed, then, once the case splits in `remove_subs` are done,
the tactic also tries `linarith` on all remaining goals. -/
meta def remove_subs (la : parse (tk "!" )?) : tactic unit := focus1 $ do
repeat (do
  some (a, b) ← list.last' <$> (target >>= get_sub),
  remove_one_sub a b ),
ite la.is_some (any_goals' $ try $ `[ linarith ]) skip

end interactive

end tactic
