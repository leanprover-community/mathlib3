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

/-- An `application` records the result of a successful application of a library lemma. -/
meta structure application :=
(state     : tactic_state)
(script    : string)
(decl      : option declaration)
(num_goals : ℕ)
(hyps_used : ℕ)

/--
The core `suggest` tactic. It attempts to apply a declaration from the library, then solve
new goals using `solve_by_elim`.

It returns a list of `application`s consisting of fields:
* `state`, a tactic state resulting from the successful application of a declaration from the library,
* `script`, a string of the form `refine ...` or `exact ...` which will reproduce that tactic state,
* `decl`, an `option declaration` indicating the declaration that was applied (or none, if `solve_by_elim` succeeded),
* `num_goals`, the number of remaining goals, and
* `hyps_used`, the number of local hypotheses used in the solution.
-/
meta def suggest_core (discharger : tactic unit := done) :
-- TODO just return an mllist!
  tactic (mllist tactic application) :=
focus1 $
do [g] ← get_goals,
   hyps ← local_context,

   -- Make sure that `solve_by_elim` doesn't just solve the goal immediately:
   (lock_tactic_state (do solve_by_elim { discharger := discharger },
          s ← read,
          m ← tactic_statement g,
          g ← instantiate_mvars g,
          return $ mllist.of_list [⟨s, m, none, 0, hyps.countp(λ h, h.occurs g)⟩])) <|>
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
   return $ (mllist.of_list defs).mfilter_map
   (λ d, lock_tactic_state $ do
     apply_declaration ff discharger d,
     ng ← num_goals,
     g ← instantiate_mvars g,
     state ← read,
     m ← message g state,
     return
     { application .
       state := state,
       decl := d.d,
       script := m,
       num_goals := ng,
       hyps_used := hyps.countp(λ h, h.occurs g) }))

meta def suggest (limit : option ℕ := none) (discharger : tactic unit := done) : tactic (list application) :=
do results ← suggest_core discharger,
   -- Get the first n elements of the successful lemmas
   L ← if h : limit.is_some then results.take (option.get h) else results.force,
   -- Sort by number of remaining goals, then by number of hypotheses used.
   return $ L.qsort(λ d₁ d₂, d₁.num_goals < d₂.num_goals ∨ (d₁.num_goals = d₂.num_goals ∧ d₁.hyps_used ≥ d₂.hyps_used))

meta def suggest_scripts (limit : option ℕ := none) (discharger : tactic unit := done) : tactic (list string) :=
do L ← suggest limit discharger,
   return $ L.map application.script

end tactic

namespace tactic.interactive
open tactic
open interactive
open lean.parser
local postfix `?`:9001 := optional

/--
`suggest` tries to apply suitable theorems/defs from the library, and generates
a list of `exact ...` or `refine ...` scripts that could be used at this step.
It leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that
`suggest` might miss some results if `num` is not large enough. However, because
`suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.
-/
meta def suggest (n : parse (with_desc "n" small_nat)?) : tactic unit :=
do L ← tactic.suggest_scripts (n.get_or_else 50),
  if is_trace_enabled_for `silence_suggest then
    if L.length = 0 then
      fail "There are no applicable declarations"
    else
      L.mmap trace >> skip
  else
    skip

end tactic.interactive
