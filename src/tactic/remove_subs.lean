/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.linarith

/-!
# `remove_subs` -- a tactic for splitting `ℕ`-subtractions

The tactic `remove_subs` looks for `ℕ`-subtractions in the goal and recursively replaces any
subexpression of the form `a - b` by two branches: one where `a ≤ b` and `a - b` is replaced
by `0` and one where `∃ c : ℕ, a = b + c` and it tries to replace `a` by `b + c`.

If called with the optional `!`-flag, then `remove_subs!` tries `linarith` on all remaining goals.

See the tactic-doc for further details.

##  Todo
*  extend the scope of `remove_subs` to include also `max/min`?  possibly even `split_ifs`?
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

/--  A convenience definition: `rw_at` rewrites at either a hypothesis or at the target. -/
meta def rw_at : option name → expr → tactic unit
| none      lem := rewrite_target lem
| (some na) lem := get_local na >>= rewrite_hyp lem >> skip

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
                           to_expr ``(nat.sub_sub %%a %%b %%c) >>= rw_at lo,
                           [ga, gb, gc] ← [a, b, c].mmap get_sub,
                           return $ local_constants_last ((a, bc) :: (ga ++ gb ++ gc))
| `(%%a - %%b)       := do infer_type a >>= is_def_eq `(ℕ),
                           [ga, gb] ← [a, b].mmap get_sub,
                           return $ local_constants_last ((a, b) :: (ga ++ gb))
| `(nat.pred %%a)    := do to_expr ``(nat.pred_eq_sub_one %%a) >>= rw_at lo,
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
  rw_at lo prf0,
  to_expr ``(@nat.sub_eq_zero_iff_le %%a %%b) >>= λ x, rewrite_hyp x prf0,
swap,
-- on the branch where `∃ c, a = b + c`...
  get_local exis >>= λ x, cases x [var, ide],
  -- either substitute `a = b + c` or rewrite `a` and then simplify the subtraction `b + c - b`
  get_local ide >>= (λ x, subst x <|> rw_at lo x),
  vare ← get_local var,
  to_expr ``(nat.add_sub_cancel_left %%b %%vare) >>= rw_at lo <|>
    fail"could not rewrite: something went wrong",
swap

/--  Similar to `repeat` except that it guarantees a number of repetitions, or fails. -/
meta def repeat_at_least : ℕ → tactic unit → tactic unit
| 0 t := repeat t
| (n + 1) t := t >> repeat_at_least n t

/--  `remove_subs_aux` acts like `remove_subs`, except that it takes a single location as input.
See the doc-string of `remove_subs` for more details. -/
meta def remove_subs_aux (la : bool) (lo : option name) : tactic unit := focus1 $ do
repeat_at_least 1 (do ht ← match lo with
                           | none    := target
                           | some na := get_local na >>= infer_type
                      end,
                      some (a, b) ← list.last' <$> (get_sub lo ht),
                      remove_one_sub lo a b),
when la $ any_goals' $ try `[ linarith ]

section error_reporting

/--  `report l la` returns `Try this: remove_subs at <subset of user input>` or
`remove_subs made no progress`, with an `!`-flag depending on `la`.
In edge-cases, it reports some variation. -/
--  `report` uses a generic `α` instead of `name`, since otherwise Lean wanted it to be `meta`.
def report {α} [decidable_eq α] [has_to_string α] (l : list (option α)) (la : bool) : string :=
let rm := "remove_subs" ++ if la then "!" else "" in
if (l = []) then ("`" ++ rm ++ "` made no progress") else
  "Try this: " ++ rm ++ if (l = [none]) then "" else " at " ++
    (" ".intercalate $ l.map $ λ a,
      dite a.is_some (λ h, has_to_string.to_string (option.get h)) (λ _, "⊢"))

end error_reporting

end remove_subs

namespace interactive
open remove_subs
setup_tactic_parser

/--
Subtraction between natural numbers in Lean is defined to be `0` when it should yield a negative
number.  The tactic `remove_subs` tries to remedy this by doing a case-split on each
`ℕ`-subtraction, depending on whether the subtraction is truncated to `0` or coincides with the
usual notion of subtraction.

`remove_subs` fails if there are unused locations, unless it is `remove_subs at *` which only
fails if it uses at most one location (and suggests the unique location via `Try this`, when
appropriate).

If `remove_subs` is called with the optional `!`-flag, then, after the case splits, the tactic
also tries `linarith` on all remaining goals. -/
meta def remove_subs (la : parse (tk "!" )?) : parse location → tactic unit
| loc.wildcard := do
  nms ← loc.get_local_pp_names loc.wildcard,
  goods ← (none :: nms.map some).mfilter $ λ x, succeeds $ remove_subs_aux la.is_some x,
  when (goods.length ≤ 1) $ fail (report goods la.is_some)
| (loc.ns xs)  := do
  goods ← xs.mfilter $ λ x, succeeds $ remove_subs_aux la.is_some x,
  when (goods.length < xs.length) $ fail (report goods la.is_some)

end interactive

end tactic

add_tactic_doc
{ name       := "remove_subs",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.remove_subs],
  tags       := ["arithmetic", "case bashing", "finishing"] }
