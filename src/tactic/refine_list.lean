 --To Do
  -- * new examples which can't be solved with `library_search`
  -- * Need another non misleading example for tactics.md
  -- * print_message/message functions as an mmap?
  -- * tests must suppress output, need a silence option like in library_Search
  -- * refine list doesn't find or_true for some reason

import tactic.library_search
import data.mllist

namespace tactic

--list_refine uses some functions from Library search
open tactic.library_search

--Run and save state function. Slightly modified version of lock_tactic_state.
--This runs a tactic and returns a tuple of the result and it's tactic state.
meta def run_and_save_state {α : Type} (t : tactic α) : tactic (α × tactic_state)
| s := match t s with
       | result.success a s' := result.success (a, s') s
       | result.exception msg pos s' := result.exception msg pos s
end

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
   print_messages g (L.map (λ d, d.1))

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
