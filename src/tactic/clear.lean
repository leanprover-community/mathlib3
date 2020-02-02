/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.core

/-!
# Better `clear` tactics

We define two variants of the standard `clear` tactic:

* `clear'` works like `clear` but the hypotheses that should be cleared can be
  given in any order. In contrast, `clear` can fail if hypotheses that depend on
  each other are given in the wrong order, even if all of them could be cleared.

* `clear_dependent` works like `clear'` but also clears any hypotheses that
  depend on the given hypotheses.

## Implementation notes

The implementation (ab)uses the native `revert_lst`, which can figure out
dependencies between hypotheses. This implementation strategy was suggested by
Simon Hudon.
-/

open native tactic interactive lean.parser

/-- Clears all the hypotheses in `hyps`. The tactic fails if any of the `hyps`
is not a local or if the target depends on any of the `hyps`.

If there are local hypotheses or definitions, say `H`, which are not in `hyps`
but depend on one of the `hyps`, what we do depends on `clear_dependent`. If it
is true, `H` is implicitly also cleared. If it is false, `clear'` fails. -/
meta def tactic.clear' (clear_dependent : bool) (hyps : expr_set) : tactic unit := do
let hyps_list := hyps.to_list,
tgt ← target,
-- Check if the target depends on any of the hyps. Doing this (instead of
-- letting one of the later tactics fail) lets us give a much more informative
-- error message.
hyps_list.mmap' (λ h, do
  dep ← kdepends_on tgt h,
  when dep $ fail $
    format!"Cannot clear hypothesis {h} since the target depends on it."),
n ← revert_lst hyps_list,
-- If revert_lst reverted more hypotheses than we wanted to clear, there must
-- have been other hypotheses dependent on some of the hyps.
when (! clear_dependent && (n ≠ hyps.size)) $ fail $ format.join
  [ "Some of the following hypotheses cannot be cleared because other "
  , "hypotheses depend on (some of) them:\n"
  , format.intercalate ", " (hyps.to_list.map to_fmt)
  ],
v ← mk_meta_var tgt,
intron n,
exact v,
gs ← get_goals,
set_goals $ v :: gs


namespace tactic.interactive

/-- Clears the given hypotheses. In contrast to `clear`, the order of hypotheses
does not matter, even if there are dependencies between them. Fails if the
target or any local hypotheses (other than the given ones) depend on the given
hypotheses. -/
meta def clear' (p : parse (many ident)) : tactic unit := do
hyps ← p.mmap get_local,
tactic.clear' false (rb_map.set_of_list hyps)

/-- Clears the given hypotheses and any other hypotheses that depend on them.
The hypotheses can be given in any order. Fails if the target depends on any of
the given hypotheses. -/
meta def clear_dependent (p : parse (many ident)) : tactic unit := do
hyps ← p.mmap get_local,
tactic.clear' true (rb_map.set_of_list hyps)

end tactic.interactive
