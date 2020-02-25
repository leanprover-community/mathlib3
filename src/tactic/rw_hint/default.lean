/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import tactic.rewrite_search.discovery
import tactic.rewrite_all
import data.mllist

open tactic.rewrite_all.congr
open tactic.rewrite_search.discovery

namespace tactic

/-- Generate a list of `rw ...` strings, which represent successful rewrites of the current goal. -/
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
meta def rw_hint (bound : ℕ := 50) : tactic (list string) :=
do
  rewrites ← mllist.of_list <$> find_all_rewrites,
  e ← target,
  successes ← (rewrites.mfilter (λ rw : expr × bool, do
    rewrite_without_new_mvars rw.1 e {symm := rw.2})).take bound,
  successes.mmap (λ p, do pp ← pp p.1, return ("rw " ++ (if p.2 then "←" else "") ++ pp.to_string))

namespace interactive

/-- Suggest possible rewrites of the current goal. -/
meta def rw_hint : tactic unit :=
tactic.rw_hint >>= list.mmap' (λ h, trace $ "Try this: " ++ h)

end interactive

-- PROJECT it would be good to have a `conv` version,
-- perhaps that only reports rewrites which transform the entire focus.

end tactic
