/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import tactic.core

namespace tactic

namespace interactive

open tactic

/-- `dec_trivial` reverts all hypotheses that occur in the target,
and attempts to close the resulting goal with `exact dec_trivial`.

Example:
```lean
example (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 :=
by dec_trivial
```
-/
meta def «dec_trivial» : tactic unit :=
do tgt ← target,
   ctx ← local_context,
   l ← ctx.mfilter (kdepends_on tgt),
   n ← revert_lst l,
   exact_dec_trivial

add_tactic_doc
{ name       := "dec_trivial",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.dec_trivial],
  tags       := ["basic", "finishing"] }

end interactive

end tactic
