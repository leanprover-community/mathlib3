-- Copyright (c) 2019 Lucas Allen. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Lucas Allen

 --To Do
  -- * new examples which can't be solved with `library_search`
  -- * Need another non misleading example for tactics.md

import tactic.library_search
import data.mllist

namespace tactic

--list_refine uses some functions from Library search
open tactic.library_search

--get state function. Returns the current state
meta def get_state : tactic tactic_state
:= λ s, result.success s s

--set state function. Sets the current state to some state
meta def set_state (s' : tactic_state) : tactic tactic_state
:= λ s, result.success s s'

--Run and save state function. Slightly modified version of lock_tactic_state.
--This runs a tactic and returns a tuple of the result and it's tactic state.
meta def run_and_save_state {α : Type} (t : tactic α) : tactic (α × tactic_state)
| s := match t s with
       | result.success a s' := result.success (a, s') s
       | result.exception msg pos s' := result.exception msg pos s
end

meta def try_assumption_and_solve_by_elim : tactic unit :=
try_core (any_goals (propositional_goal >> assumption)) >>
  try_core (solve_by_elim { all_goals := tt }) >>
  skip

--This function prints the apply tactic with the corresponding lemma/theorem with inputs
meta def message (l : decl_data × tactic_state) (g : expr) : tactic string :=
do s ← get_state,
   set_state l.2,
   r ← tactic_statement g,
   set_state s,
   return r

--Runs through the list of things and prints a message for each one
meta def print_messages (g : expr) : list (decl_data × tactic_state) → tactic string
| []      := return ""
| (l::ls) := do message l g >>= trace,
                print_messages ls

meta def get_mldefs (defs : list decl_data) : mllist tactic decl_data :=
mllist.of_list defs

--The main list_refine tactic, this is very similar to the main Library_search function
meta def refine_list (num : ℕ := 50) : tactic string :=
do (g::gs) ← get_goals,
   t ← infer_type g,

   -- Collect all definitions with the correct head symbol
   defs ← library_defs (head_symbol t),
   -- Sort by length; people like short proofs
   let defs := defs.qsort(λ d₁ d₂, d₁.l ≤ d₂.l),
   -- Turn defs into an mllist
   let mldefs := get_mldefs defs,
   -- Filter out the lemmas that cannot be used with refine
   let results := mldefs.mfilter_map
     (λ d, run_and_save_state ((apply_declaration try_assumption_and_solve_by_elim d) >> pure d)),
   let results_with_num_goals := results.mmap
        (λ d, lock_tactic_state $ do set_state d.2, ng ← num_goals, return (d, ng)),
   -- Get the first num elements of the successful lemmas
   L ← results_with_num_goals.take num,
   let L := L.qsort(λ d₁ d₂, d₁.2 ≤ d₂.2),
   -- Print the fist num successful lemmas
   if L.length = 0 then do
    let r := "There are no applicable lemmas or theorems",
    trace r,
    return r
   else
   if (¬ is_trace_enabled_for `silence_library_search)
   then print_messages g (L.map (λ d, d.1))
   else return ""

end tactic

namespace interactive
/--
`refine_list` is a modification of `library_search`, which lists possible usages of the `refine`
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
