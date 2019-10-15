-- Copyright (c) 2019 Lucas Allen. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Lucas Allen

import tactic.library_search
import data.mllist

/-
`refine_list` is an extension of `library_search` which lists some applicable lemmas and theorems.
-/

namespace tactic

--list_refine uses some functions from library_search
open tactic.library_search

/--This function prints either the `exact` or `refine` tactics with the corresponding
lemma/theorem with inputs for a specific tactic_state-/
meta def message (l : decl_data × tactic_state) (g : expr) : tactic string :=
do s ← read,
   write l.2,
   r ← tactic_statement g,
   write s,
   return r

/--Runs through the list of tactic_states and prints an `exact` or `refine` message for each one-/
meta def print_messages (g : expr) (silent : bool) : list (decl_data × tactic_state) → tactic (list string)
| []      := return []
| (l::ls) := do r ← message l g,
                if ¬ silent then trace r else skip,
                rs ← print_messages ls,
                return (r :: rs)

/-- Returns a monadic lazy list of declaration data -/
meta def get_mldefs (defs : list decl_data) : mllist tactic decl_data :=
mllist.of_list defs


declare_trace silence_refine_list -- Turn off `exact ...` trace message
declare_trace refine_list         -- Trace a list of all relevant lemmas

/-- The main refine_list tactic, this is very similar to the main library_search function. It returns
a list of strings consisting of possible applications of the refine tactic. The length of the list is
no longer than num.-/
meta def refine_list (num : ℕ := 50) (discharger : tactic unit := done) : tactic (list string) :=
do (g::gs) ← get_goals,
   t ← infer_type g,

   -- Make sure that `solve_by_elim` doesn't just solve the goal immediately:
   (do
       r ← lock_tactic_state (solve_by_elim { discharger := discharger } >> tactic_statement g),
       when (¬ is_trace_enabled_for `silence_refine_list) $ tactic.trace r,
       return $ [to_string r]) <|>
   -- Otherwise, let's actually try applying library lemmas.
   (do
   -- Collect all definitions with the correct head symbol
   defs ← library_defs (head_symbol t),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   when (is_trace_enabled_for `refine_list) $ (do
     trace format!"Found {defs.length} relevant lemmas:",
     trace $ defs.map (λ ⟨d, n, m, l⟩, (n, m.to_string))),
   -- Turn defs into an mllist
   let mldefs := get_mldefs defs,

  --  -- PROJECT it would be better to sort not just by `num_goals`, but by the pair
  --  -- `(num_goals, -num_hyps_used)`, where `num_hyps_used` is a putative function that
  --  -- counts numbers of appearances of local hypotheses in `result`.

   -- Filter out the lemmas that cannot be used with refine
   let results_with_num_goals := mldefs.mfilter_map
   (λ d, lock_tactic_state $ do
     apply_declaration ff discharger d,
     ng ← num_goals,
     state ← read,
     return ((d, state), ng)),
   -- Get the first num elements of the successful lemmas
   L ← results_with_num_goals.take num,
   let L := L.qsort(λ d₁ d₂, d₁.2 ≤ d₂.2),
   -- Print the first num successful lemmas
   if L.length = 0 then do
    fail "There are no applicable lemmas or theorems"
   else
    print_messages g (is_trace_enabled_for `silence_refine_list) (L.map (λ d, d.1)))

end tactic

namespace interactive
/--
`refine_list` lists possible usages of the `refine`
tactic and leaves the tactic state unchanged. It is intended as a complement of the search
function in your editor, the `#find` tactic, and `library_search`.

`refine_list` takes an optional natural number `num` as input and returns the first `num`
(or less, if all possibilities are exhausted) possibilities ordered by length of lemma names.
The default for `num` is `50`.
For performance reasons `refine_list` uses monadic lazy lists (`mllist`). This means that
`refine_list` might miss some results if `num` is not large enough. However, because
`refine_list` uses monadic lazy lists, smaller values of `num` run faster than larger values.
-/
meta def refine_list := tactic.refine_list

end interactive
