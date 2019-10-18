/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen and Scott Morrison
-/

import tactic.library_search
import data.mllist

/-!
`suggest` is an extension of `library_search` which lists some applicable lemmas and theorems.
-/

namespace tactic

open tactic.library_search

/--
Assuming that a goal `g` has been (partially) solved in the tactic_state `l`,
this function prepares a string of the form `exact ...` or `refine ...` (possibly with underscores)
that will reproduce that result.
-/
meta def message (g : expr) (l : tactic_state) : tactic string :=
do s ← read,
   write l,
   r ← tactic_statement g,
   write s,
   return r

/--
Runs through the list of tactic_states in which the goal `g` has been (partially) solved,
and generates an `exact ...` or `refine ...` message for each one.
-/
meta def messages (g : expr) (L : list tactic_state) : tactic (list string) :=
L.mmap (message g)

declare_trace silence_suggest -- Turn off `exact/refine ...` trace messages
declare_trace suggest         -- Trace a list of all relevant lemmas

/--
The main `suggest` tactic, which is very similar to the main `library_search` function.
It returns a list of pairs `(state, message)` consisting of
* `state`, a tactic state resulting from the successful application of a declaration from the library, and
* `message`, a string of the form `refine ...` or `exact ...` which will reproduce that tactic state.
-/
meta def suggest (limit : option ℕ := none) (discharger : tactic unit := done) : tactic (list (tactic_state × string)) :=
do [g] ← get_goals | fail "`suggest` should be called with exactly one goal",
   hyps ← local_context,

   -- Make sure that `solve_by_elim` doesn't just solve the goal immediately:
   (do
    r ← lock_tactic_state
      (do solve_by_elim { discharger := discharger },
          s ← read,
          m ← tactic_statement g,
          return (s, m)),
    return $ [r]) <|>
   -- Otherwise, let's actually try applying library lemmas.
   (do
   -- Collect all definitions with the correct head symbol
   t ← infer_type g,
   defs ← library_defs (head_symbol t),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   when (is_trace_enabled_for `suggest) $ (do
     trace format!"Found {defs.length} relevant lemmas:",
     trace $ defs.map (λ ⟨d, n, m, l⟩, (n, m.to_string))),

   -- Try applying each lemma against the goal,
   -- then record the number of remaining goals, and number of local hypotheses used.
   let results := (mllist.of_list defs).mfilter_map
   (λ d, lock_tactic_state $ do
     apply_declaration ff discharger d,
     ng ← num_goals,
     g ← instantiate_mvars g,
     let nh := hyps.countp(λ h, h.occurs g), -- number of local hypotheses used
     state ← read,
     return ((d, state), (ng, nh))),
   -- Get the first n elements of the successful lemmas
   L ← if h : limit.is_some then results.take (option.get h) else results.force,
   -- Sort by number of remaining goals, then by number of hypotheses used.
   let L := L.qsort(λ d₁ d₂, d₁.2.1 < d₂.2.1 ∨ (d₁.2.1 = d₂.2.1 ∧ d₁.2.2 ≥ d₂.2.2)),
   -- Generate messages for the successful applications
   L.mmap (λ d, do m ← message g d.1.2, return (d.1.2, m)))

end tactic

namespace tactic.interactive
open tactic
open interactive
open lean.parser
local postfix `?`:9001 := optional

/--
`suggest` lists possible usages of the `exact` or `refine`
tactic and leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that
`suggest` might miss some results if `num` is not large enough. However, because
`suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.
-/
meta def suggest (n : parse (with_desc "n" small_nat)?) : tactic unit :=
do L ← tactic.suggest (n.get_or_else 50),
  if is_trace_enabled_for `silence_suggest then
    if L.length = 0 then
      fail "There are no applicable declarations"
    else
      L.mmap (λ p, trace p.2) >> skip
  else
    skip

end tactic.interactive
