-- Copyright (c) 2018 Keeley Hoek. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison
import data.option.defs data.mllist

open tactic

@[derive decidable_eq]
inductive side
| L
| R

def side.other : side → side
| side.L := side.R
| side.R := side.L

def side.to_string : side → string
| side.L := "L"
| side.R := "R"

instance : has_to_string side := ⟨side.to_string⟩

namespace tactic.rewrite_all

meta structure cfg extends rewrite_cfg :=
(try_simp   : bool := ff)
(discharger : tactic unit := skip)
 -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
(simplifier : expr → tactic (expr × expr) := λ e, failed)

meta structure tracked_rewrite :=
(exp : expr)
(proof : tactic expr)
-- If `addr` is not provided by the underlying implementation of `rewrite_all` (i.e. kabstract)
-- `rewrite_search` will not be able to produce tactic scripts.
(addr : option (list side))

end tactic.rewrite_all
