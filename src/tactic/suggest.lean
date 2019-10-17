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
meta def message (l : tactic_state) (g : expr) : tactic string :=
do s ← read,
   write l,
   r ← tactic_statement g,
   write s,
   return r

/--
Runs through the list of tactic_states in which the goal `g` has been (partially) solved,
and prints an `exact ...` or `refine ...` message for each one.
-/
meta def print_messages (g : expr) (silent : bool) : list tactic_state → tactic (list string)
| []      := return []
| (l::ls) := do r ← message l g,
                if ¬ silent then trace r else skip,
                rs ← print_messages ls,
                return (r :: rs)

declare_trace silence_suggest -- Turn off `exact/refine ...` trace messages
declare_trace suggest         -- Trace a list of all relevant lemmas

/--
The main `suggest` tactic, which is very similar to the main `library_search` function. It returns
a list of strings consisting of possible applications of the refine tactic. The length of the list is
no longer than num.
-/
meta def suggest (num : ℕ := 50) (discharger : tactic unit := done) : tactic (list string) :=
do (g::gs) ← get_goals,
   t ← infer_type g,
   hyps ← local_context,

   -- Make sure that `solve_by_elim` doesn't just solve the goal immediately:
   (do
       r ← lock_tactic_state (solve_by_elim { discharger := discharger } >> tactic_statement g),
       when (¬ is_trace_enabled_for `silence_suggest) $ tactic.trace r,
       return $ [to_string r]) <|>
   -- Otherwise, let's actually try applying library lemmas.
   (do
   -- Collect all definitions with the correct head symbol
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
   -- Get the first num elements of the successful lemmas
   L ← results.take num,
   -- Sort by number of remaining goals, then by number of hypotheses used.
   let L := L.qsort(λ d₁ d₂, d₁.2.1 < d₂.2.1 ∨ (d₁.2.1 = d₂.2.1 ∧ d₁.2.2 ≥ d₂.2.2)),
   -- Print the first num successful lemmas
   if L.length = 0 then
     fail "There are no applicable lemmas or theorems"
   else
     print_messages g (is_trace_enabled_for `silence_suggest) (L.map (λ d, d.1.2)))

end tactic

namespace tactic.interactive
open interactive
open lean.parser

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
meta def suggest (n : parse (with_desc "n" small_nat)) : tactic unit := tactic.suggest n >> tactic.skip

end tactic.interactive
