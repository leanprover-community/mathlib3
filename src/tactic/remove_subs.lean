/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.linarith

/-!
# `remove_subs` -- a tactic for splitting nat-subtractions

Subtraction between natural numbers is defined to be `0` when it should yield a negative number.
The tactic `remove_subs` tries to remedy this by doing a case-split on each nat-subtractions,
depending on whether the subtraction is truncated to `0` or coincides with the usual notion of
subtraction.

See the tactic-doc for more details.
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
subexpression of `e`.  While doing this, it also assumes that `e` was the target and rewrites the
target to reduce the number of nat-subtractions, using the identity `a - b - c = a - (b + c)`. -/
meta def get_sub : expr → tactic (list (expr × expr))
| `(%%a - %%b - %%c) := do bc ← to_expr ``(%%b + %%c),
                           to_expr ``(nat.sub_sub %%a %%b %%c) >>= rewrite_target,
                           [ga, gb, gc] ← [a, b, c].mmap get_sub,
                           return ((a, bc) :: (ga ++ gb ++ gc))
| `(%%a - %%b)       := do [ga, gb] ← [a, b].mmap get_sub,
                           return ((a, b) :: (ga ++ gb))
| `(nat.pred %%a)    := do to_expr ``(nat.pred_eq_sub_one) >>= rewrite_target,
                           ga ← get_sub a,
                           return ((a, `(1)) :: ga)
| (expr.app f a)     := do [gf, ga] ← [f, a].mmap get_sub,
                           return (gf ++ ga)
| _                  := pure []

/--  `remove_one_sub a b` assumes that the expression `a - b` occurs in the target.
It splits two cases:
*  `a ≤ b`, in which case it replaces `a - b` with `0` and introduces the inequality `a ≤ b` into
   the local context;
*  writes `a = b + c`, for some `c` and tries to substitute this equality.
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

/--  The tactic `remove_subs` looks for nat-subtractions in the goal and it recursively replaces
any subexpression of the form `a - b` by two branches: one where `a ≤ b` and `a - b` is replaced
by `0` and one where `b < a` and it tries to replace `a` by `b + c`, for some `c : ℕ`.

If `remove_subs` is called with the optional flag `!`, then, after the case splits, the tactic
also tries `linarith` on all remaining goals. -/
meta def remove_subs (la : parse (tk "!" )?) : tactic unit := focus1 $ do
repeat (do
  some (a, b) ← list.last' <$> (target >>= get_sub),
  remove_one_sub a b ),
if la.is_some then (any_goals' $ try $ `[ linarith ]) else skip

end interactive

end tactic

add_tactic_doc
{ name       := "remove_subs",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.remove_subs],
  tags       := ["arithmetic", "case bashing", "finishing"] }
