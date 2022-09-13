/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import tactic.core
import tactic.dependencies

namespace tactic

meta def take_pi_args : nat → expr → list name
| (n+1) (expr.pi h _ _ e) := h :: take_pi_args n e
| _ _ := []

namespace interactive
setup_tactic_parser

meta def doneif (H : parse ident) (t : parse (tk ":" *> texpr))
  (revert : parse (
    (tk "generalizing" *> ((none <$ tk "*") <|> some <$> ident*)) <|> pure (some [])))
  (h : parse (tk "using" *> ident)?) :
  tactic unit := do
  let h := h.get_or_else `this,
  t ← i_to_expr ``(%%t : Sort*),
  (num_generalized, goal, rctx) ← retrieve (do
    assert_core H t, swap,
    num_generalized ← match revert with
    | none := revert_all
    | some revert := prod.fst <$> (revert.mmap tactic.get_local >>= revert_lst')
    end,
    goal ← target,
    ctx ← local_context,
    return (num_generalized, goal, ctx)),
  ctx ← local_context,
  e ← tactic.assert h goal,
  goal ← target,
  (take_pi_args num_generalized goal).reverse.mmap' $ λ h,
    try (tactic.get_local h >>= tactic.clear),
  intron (num_generalized + 1),
  swap,
  tactic.by_cases t H,
  H ← tactic.get_local H,
  let L := ctx.filter (λ n, n ∉ rctx),
  tactic.exact $ (e.mk_app L).app H,
  swap

meta def wlog (H : parse ident) (t : parse (tk ":" *> texpr))
  (revert : parse (
    (tk "generalizing" *> ((none <$ tk "*") <|> some <$> ident*)) <|> pure none))
  (h : parse (tk "using" *> ident)?) :
  tactic unit :=
doneif H t revert h >> swap

end interactive
end tactic
