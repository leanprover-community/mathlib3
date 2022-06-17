/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Keeley Hoek, Scott Morrison
-/
import meta.expr_lens

namespace tactic
open expr

namespace nth_rewrite

/-- Configuration options for nth_rewrite. -/
meta structure cfg extends rewrite_cfg :=
(try_simp   : bool := ff)
(discharger : tactic unit := skip)
 -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
(simplifier : expr → tactic (expr × expr) := λ e, failed)

/-- A data structure to track rewrites of subexpressions.
The field `exp` contains the new expression,
while `proof` contains a proof that `exp` is equivalent to the expression that was rewritten. -/
meta structure tracked_rewrite :=
(exp : expr)
(proof : tactic expr)
-- If `addr` is not provided by the underlying implementation of `nth_rewrite` (i.e. kabstract)
-- `rewrite_search` will not be able to produce tactic scripts.
(addr : option (list expr_lens.dir))

namespace tracked_rewrite

/-- Postprocess a tracked rewrite into a pair
of a rewritten expression and a proof witness of the rewrite. -/
meta def eval (rw : tracked_rewrite) : tactic (expr × expr) :=
do prf ← rw.proof,
   return (rw.exp, prf)

end tracked_rewrite

end nth_rewrite

end tactic
