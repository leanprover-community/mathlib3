/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.linarith

/-!
# `remove_subs` -- a tactic for splitting `ℕ`-subtractions

Subtraction between natural numbers is defined to be `0` when it should yield a negative number.
The tactic `remove_subs` tries to remedy this by doing a case-split on each `ℕ`-subtraction,
depending on whether the subtraction is truncated to `0` or coincides with the usual notion of
subtraction.

See the tactic-doc for more details.

##  Todo
*  allow `remove_subs` to work `at` some hypotheses?
-/

namespace tactic
namespace remove_subs

lemma nat.le_cases (a b : ℕ) : a - b = 0 ∨ ∃ c, a = b + c :=
begin
  by_cases ab : a ≤ b,
  { exact or.inl (tsub_eq_zero_of_le ab) },
  { refine or.inr _,
    rcases nat.exists_eq_add_of_le ((not_le.mp ab).le) with ⟨c, rfl⟩,
    exact ⟨_, rfl⟩ },
end

/--  Given a list `l` of pairs of expressions, `local_constants_last l` reorders the list `l`
so that all pairs `(a,b) ∈ l` with `a` a local constant appear last.  This is used in `get_sub`
so that the replacement of the `ℕ`-subtractions begins with subtractions where an old term
can be substituted, rather than simply rewritten. -/
meta def local_constants_last (l : list (expr × expr)) : list (expr × expr) :=
let (csts, not_csts) := l.partition (λ e : expr × expr, e.1.is_local_constant) in not_csts ++ csts

/--  `get_sub e` extracts a list of pairs `(a, b)` from the expression `e`, where `a - b` is a
subexpression of `e`.  While doing this, it also assumes that
* the initial input `e` was the target and rewrites it to reduce the number of `ℕ`-subtractions,
  using the identity `a - b - c = a - (b + c)`;
* the subtractions that get extracted are subtractions in `ℕ`.
-/
meta def get_sub (lo : option name) : expr → tactic (list (expr × expr))
| `(%%a - %%b - %%c) := do bc ← to_expr ``(%%b + %%c),
                           lem ← to_expr ``(nat.sub_sub %%a %%b %%c),
                           match lo with
                           | none    := rewrite_target lem
                           | some na := get_local na >>= rewrite_hyp lem >> skip
                           end,
                           [ga, gb, gc] ← [a, b, c].mmap get_sub,
                           return $ local_constants_last ((a, bc) :: (ga ++ gb ++ gc))
| `(%%a - %%b)       := do infer_type a >>= is_def_eq `(ℕ),
                           [ga, gb] ← [a, b].mmap get_sub,
                           return $ local_constants_last ((a, b) :: (ga ++ gb))
| `(nat.pred %%a)    := do lem ← to_expr ``(nat.pred_eq_sub_one %%a),
                           match lo with
                           | none    := rewrite_target lem
                           | some na := get_local na >>= rewrite_hyp lem >> skip
                           end,
                           ga ← get_sub a,
                           return $ local_constants_last ((a, `(1)) :: ga)
| (expr.app f a)     := local_constants_last <$>
                          ((++) <$> (get_sub f <|> pure []) <*> (get_sub a <|> pure []))
| _                  := pure []

/--  `remove_one_sub a b` assumes that the expression `a - b` occurs in the target.
It splits two cases:
*  if `a ≤ b`, then it replaces `a - b` with `0` and introduces the inequality `a ≤ b` into
   the local context;
*  otherwise, it writes `a = b + c`, for some `c` and tries to substitute this equality.
-/
meta def remove_one_sub (lo : option name) (a b : expr) : tactic unit := do
-- introduce names with the following meanings:
-- `eq0 : a - b = 0`, `exis : ∃ c, a = b + c`, `var = c`, `ide : a = b + c`
[eq0, exis, var, ide] ← ["h", "k", "x", "hx"].mmap (λ y, get_unused_name y),
-- either `a ≤ b` or `∃ c, a = b + c`
cases `(nat.le_cases %%a %%b) [eq0, exis],
-- on the branch where `a ≤ b`...
  prf0 ← get_local eq0,
  match lo with
  | none    := rewrite_target prf0
  | some na := get_local na >>= rewrite_hyp prf0 >> skip
  end,
  to_expr ``(@nat.sub_eq_zero_iff_le %%a %%b) >>= λ x, rewrite_hyp x prf0,
swap,
-- on the branch where `∃ c, a = b + c`...
  get_local exis >>= λ x, cases x [var, ide],
  [vare, lide] ← [var, ide].mmap get_local,
  lem ← to_expr ``(nat.add_sub_cancel_left %%b %%vare),
  -- either substitute or rewrite `a` and then clear the subtraction
  match lo with
  | none    := do subst lide <|> rewrite_target lide,
                  rewrite_target lem <|> fail"could not rewrite: something went wrong"
  | some na := do nah ← get_local na,
                  subst lide <|> rewrite_hyp lide nah >> skip,
                  nah ← get_local na,  -- again, since the previous step changed its type!
                  rewrite_hyp lem nah >> skip <|> fail"could not rewrite: something went wrong"
  end,
swap

end remove_subs

namespace interactive
open remove_subs
setup_tactic_parser

/--  The tactic `remove_subs` looks for `ℕ`-subtractions in the goal and it recursively replaces
any subexpression of the form `a - b` by two branches: one where `a ≤ b` and `a - b` is replaced
by `0` and one where `∃ c : ℕ, a = b + c` and it tries to replace `a` by `b + c`.

`remove_subs` fails if there are no `ℕ`-subtractions.

If `remove_subs` is called with the optional flag `!`, then, after the case splits, the tactic
also tries `linarith` on all remaining goals. -/
meta def remove_subs (la : parse (tk "!" )?) (lo : option name) : tactic unit := focus1 $ do
ht ← match lo with
  | none    := target
  | some na := get_local na >>= infer_type
end,
(a, b) ← (do subs ← get_sub lo ht,
             list.last' subs) <|> fail"no ℕ-subtraction found",
remove_one_sub lo a b,
repeat (do
ht ← match lo with
  | none    := target
  | some na := get_local na >>= infer_type
end,
  some (a, b) ← list.last' <$> (get_sub lo ht),
  remove_one_sub lo a b ),
when la.is_some $ any_goals' $ try `[ linarith ]

end interactive

end tactic

add_tactic_doc
{ name       := "remove_subs",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.remove_subs],
  tags       := ["arithmetic", "case bashing", "finishing"] }
