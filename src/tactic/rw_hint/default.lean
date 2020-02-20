/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import tactic.rewrite_search.discovery
import tactic.rewrite_all

open tactic.rewrite_all.congr
open tactic.rewrite_search.discovery

namespace tactic

/-- Generate a list of `rw ...` strings, which represent successful rewrites of the current goal. -/
-- TODO perhaps run `solve_by_elim` on resulting goals,
-- and put any rewrites where this succeeds at the top of the list?
meta def rw_hint : tactic (list string) :=
do
  rewrites ← find_all_rewrites,
  e ← target,
  successes ← rewrites.mfilter (λ rw, do
    res ← try_core $ rewrite_without_new_mvars rw.1 e {symm := rw.2},
    return res.is_some),
  successes.mmap (λ p, do pp ← pp p.1, return ("rw " ++ (if p.2 then "←" else "") ++ pp.to_string))

namespace interactive

/-- Suggest possible rewrites of the current goal. -/
meta def rw_hint : tactic unit :=
do hints ← tactic.rw_hint,
   hints.mmap (λ h, trace $ "Try this: " ++ h),
   skip

end interactive

end tactic
