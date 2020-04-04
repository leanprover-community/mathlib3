/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import tactic.rewrite_search.discovery
import tactic.rewrite_all
import tactic.core
import data.mllist

/-!
## rw_hint

The tactic `rw_hint` will try to rewrite the goal using all available lemmas and hypotheses,
reporting those that make progress.

```
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q :=
begin
  rw_hint, -- Prints "Try this: rw ←h"
  rw ←h, exact p,
end
```

The optional syntax `rw_hint with p` only reports rewrites that transform the goal
to something containing the pattern `p`.
(So for example one could write `rw_hint with _ ∧ _` to find rewrites producing a
goal containing a conjunction.)

Users should be careful that this is a blunt tool:
* with many imports open it can be very slow,
* with 'generic' goals (in particular anything involving numerals) you will get many
  spurious suggestions.

There is also a `conv` mode, which may be more useful: it only reports rewrites that transform the
entire current focus, so if you expect to be able to rewrite some particular subexpression using a
lemma, you can use `congr` and `skip` inside `conv` to focus on that subexpression, and then call
`rw_hint`, which hopefully will then return fewer false positives than `rw_hint` on the entire
original goal. Inside `conv`, calling `rw_hint with p` will require that the rewritten
focus matches the pattern `p`, rather than merely the pattern `p` appearing as a subexpression.

The main use case for `rw_hint` is for users with some familiarity with the mathlib naming
conventions, who may be able to scan through a list of suggestions and quickly recognise from the
names which are the actually relevant suggestions. Beginners unfamiliar with these conventions may
find `rw_hint` unhelpful.
-/

open tactic.rewrite_all.congr
open tactic.rewrite_search.discovery

namespace tactic

/--
Generate a list of at most `bound` pairs strings of the form `("rw ...", "new_goal")`,
which represent successful rewrites of the current goal.

If `entire := tt`, only report rewrites which modify the entire goal.
(This is usede in the interactive `conv` tactic.)
-/
-- TODO perhaps run `solve_by_elim` on resulting goals,
-- and put any rewrites where this succeeds at the top of the list?
-- This is probably far too slow, but perhaps worth investigating.
-- TODO some suggestions will appear for any equality goal, but are stupid:
--   Try this: rw eq_comm
--   Try this: rw ←option.some_inj
--   Try this: rw ←eq_comm
--   Try this: rw ←eq_iff_eq_cancel_right
--   Try this: rw ←eq_iff_eq_cancel_left
--   Try this: rw ←option.some.inj_eq
--   Try this: rw ←heq_iff_eq
-- Is there a sensible way to discard these? Otherwise we could blacklist them?
meta def rw_hint (e : expr) (entire : bool := ff) (for : option pexpr := none) (bound : ℕ := 50) : tactic (list (string × string)) :=
do
  rewrites ← mllist.of_list <$> find_all_rewrites,
  successes ← (rewrites.mfilter_map (λ rw : expr × bool, do
    (n, p) ← rewrite_without_new_mvars rw.1 e {symm := rw.2},
    guard $ ¬entire ∨ rewrite_is_of_entire p,
    match for with
    | some p := (if entire then match_expr p n else match_subexpr p n) >> skip
    | none   := skip
    end,
    return (rw, n))).take bound,
  successes.mmap (λ p, do
    rw_pp ← pp p.1.1,
    ng_pp ← pp p.2,
    return ("rw " ++ (if p.1.2 then "←" else "") ++ rw_pp.to_string, ng_pp.to_string))

/-- Runs `rw_hint` on the current goal. -/
meta def rw_hint_target (for : option pexpr := none) :=
target >>= (λ e, rw_hint e ff for)

open interactive lean.parser interactive.types expr tactic
local postfix `?`:9001 := optional

namespace interactive

/--
Suggest possible rewrites of the current goal, using all lemmas in the environment.

The optional syntax `rw_hint with p` only reports rewrites that transform the goal
to something containing the pattern `p`.
(So for example one could write `rw_hint with _ ∧ _` to find rewrites producing a
goal containing a conjunction.)

See also the related `conv` mode tactic, which requires that the rewrite (and optional guard pattern)
exactly matches the current focus, rather than some subexpression.

Users should be careful that `rw_hint` is a blunt tool:
* with many imports open it can be very slow,
* with 'generic' goals (in particular anything involving numerals) you will get many
  spurious suggestions.

The main use case is for users with some familiarity with the mathlib naming conventions,
who may be able to scan through a list of suggestions and quickly recognise from the
names which are the actually relevant suggestions. Beginners unfamiliar with these
conventions may find `rw_hint` unhelpful.
-/
meta def rw_hint (for : parse (tk "with" *> texpr)?) : tactic unit :=
do hints ← rw_hint_target for,
   guard (hints.length > 0) <|> fail "No rewrites found",
   hints.mmap' (λ h, trace $ "Try this: " ++ h.1 ++ " -- " ++ h.2)


add_tactic_doc
{ name        := "rw_hint",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.rw_hint],
  tags        := ["rewriting", "search", "Try this"] }

end interactive

end tactic

namespace conv

open interactive lean.parser interactive.types expr tactic
local postfix `?`:9001 := optional

namespace interactive

/--
Suggest possible rewrites of the current focus, using all lemmas in the environment.
Only rewrites that transform the entire focus (rather than subexpressions) are
reported while in `conv` mode.

The optional syntax `rw_hint with p` only reports rewrites that transform the focus
to something matching the pattern `p`.
(So for example one could write `rw_hint with _ ∧ _` to find rewrites producing a conjunction.)

See also the interactive tactic `rw_hint`.
-/
meta def rw_hint (for : parse (tk "with" *> texpr)?) : conv unit :=
lhs >>= (λ e, tactic.rw_hint e tt for) >>= list.mmap' (λ h, tactic.trace $ "Try this: " ++ h.1 ++ " -- " ++ h.2)

end interactive
end conv
