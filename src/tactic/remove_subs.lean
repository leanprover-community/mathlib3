/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.linarith

/-!
# `remove_subs` -- a tactic for splitting truncated subtractions

The tactic `remove_subs` looks for truncated subtractions in the goal or `at` one or more
hypotheses and recursively replaces any subexpression of the form `a - b` by two branches:
* one where `a ≤ b` and `a - b` is replaced by `0` and
* one where `∃ c : ℕ, a = b + c` and it tries to replace `a` by `b + c`.

If called with the optional `!`-flag, then `remove_subs!` tries `linarith` on all remaining goals.

See the tactic-doc for further details.

##  Todo
*  extend the scope of `remove_subs` to include also `max/min`?  possibly even `split_ifs`?
-/

namespace tactic
namespace remove_subs

lemma le_cases {R} [canonically_linear_ordered_add_monoid R] [has_sub R] [has_ordered_sub R]
  (a b : R) :
  a - b = 0 ∨ ∃ c, a = b + c :=
begin
  by_cases ab : a ≤ b,
  { exact or.inl (tsub_eq_zero_of_le ab) },
  { rcases exists_add_of_le (not_le.mp ab).le with ⟨c, rfl⟩,
    exact or.inr ⟨_, rfl⟩ },
end

/--  A convenience definition: `rw_at` rewrites either at a hypothesis or at the target. -/
meta def rw_at : option name → expr → tactic unit
| none      lem := rewrite_target lem
| (some na) lem := get_local na >>= rewrite_hyp lem >> skip

/--  `get_sub lo e` extracts a list of pairs `(a, b)` from the expression `e`, where `a - b` is a
subexpression of `e`.  It also takes argument `lo : option name`, informing it that the initial
input `e` is hypothesis `na`, if `lo = some na`, or the goal, if `lo = none`.  The tactic
rewrites this location to reduce the number of truncated subtractions, using the identity
`a - b - c = a - (b + c)`. -/
meta def get_sub (lo : option name) : expr → tactic (list (expr × expr))
| `(%%a - %%b - %%c) := do to_expr ``(tsub_tsub %%a %%b %%c) >>= rw_at lo,
                           bc ← to_expr ``(%%b + %%c),
                           [ga, gb, gc] ← [a, b, c].mmap get_sub,
                           return ((a, bc) :: (ga ++ gb ++ gc))
| `(%%a - %%b)       := do [ga, gb] ← [a, b].mmap get_sub,
                           return ((a, b) :: (ga ++ gb))
| `(nat.pred %%a)    := do rw_at lo `(nat.pred_eq_sub_one %%a),
                           ga ← get_sub a,
                           return ((a, `(1)) :: ga)
| (expr.app f a)     := (++) <$> (get_sub f <|> pure []) <*> get_sub a <|> pure []
| _                  := pure []

/--  `remove_one_sub lo a b` assumes that the expression `a - b` occurs in hypothesis `lo`.
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
to_expr ``(le_cases %%a %%b) >>= λ x, cases x [eq0, exis],
-- on the branch where `a ≤ b`...
  prf0 ← get_local eq0,
  rw_at lo prf0,
  to_expr ``(@tsub_eq_zero_iff_le _ _ _ _ %%a %%b) >>= λ x, rewrite_hyp x prf0,
swap,
-- on the branch where `∃ c, a = b + c`...
  get_local exis >>= λ x, cases x [var, ide],
  -- either substitute `a = b + c` or rewrite `a`, after which simplify the subtraction `b + c - b`
  get_local ide >>= (λ x, subst x <|> rw_at lo x),
  vare ← get_local var,
  to_expr ``(add_tsub_cancel_left %%b %%vare) >>= rw_at lo,
swap

/--  Similar to `repeat` except that it guarantees a number of repetitions, or fails. -/
meta def repeat_at_least : ℕ → tactic unit → tactic unit
| 0 t := repeat t
| (n + 1) t := t >> repeat_at_least n t

/--  `remove_subs_aux la lo` acts like `remove_subs`, except that it acts at the single hypothesis
`lo`.  The input `la` is used to know if `linarith` should be called at the end.
See the doc-string of `remove_subs` for more details. -/
meta def remove_subs_aux (la : bool) (lo : option name) : tactic unit := focus1 $ do
repeat_at_least 1 (do
  ht ← match lo with
       | none    := target
       | some na := get_local na >>= infer_type
  end,
  subs ← get_sub lo ht,  -- extract all subtractions
  -- move all subtractions `a - b` with `a` a local constant last, so that `remove_one_sub`
  -- uses `subst` instead of `rw` (when it can)
  some (a, b) ← pure $ let (csts, not_csts) := subs.partition
    (λ e : expr × expr, e.1.is_local_constant) in (not_csts ++ csts).last',
  remove_one_sub lo a b),
when la $ any_goals' $ try `[ linarith ]

section error_reporting

/--  `report l la` returns `Try this: remove_subs at <subset of user input>` or
`'remove_subs' made no progress`, with an `!`-flag depending on `la`.
In edge-cases, it reports some variation. -/
def report (l : list (option name)) (la : bool) : string :=
let rm := "remove_subs" ++ if la then "!" else "" in match l with
| []     :=          "'" ++ rm ++ "' made no progress"
| [none] := "Try this: " ++ rm
| l      := "Try this: " ++ rm ++ " at " ++ (" ".intercalate $ l.map $ λ a,
              dite a.is_some (λ h, has_to_string.to_string (option.get h)) (λ _, "⊢"))
end

end error_reporting

end remove_subs

namespace interactive
open remove_subs
setup_tactic_parser

/--
Subtraction between natural numbers in Lean is defined to be `0` when it should yield a negative
number.  The tactic `remove_subs` tries to remedy this by doing a case-split on each
truncated subtraction, depending on whether the subtraction is truncated to `0` or coincides with
the usual notion of subtraction.

`remove_subs` fails if there are unused locations, unless it is `remove_subs at *` which only
fails if it uses at most one location (and suggests the unique location via `Try this`, when
appropriate).

If `remove_subs` is called with the optional `!`-flag, then, after the case splits, the tactic
also tries `linarith` on all remaining goals.

The tactic works not only on `ℕ`, but on any `canonically_linear_ordered_add_monoid` `R` with
`has_sub R` and `has_ordered_sub R`. -/
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
