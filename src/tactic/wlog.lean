/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import tactic.core

namespace tactic

meta def take_pi_args : nat → expr → list name
| (n+1) (expr.pi h _ _ e) := h :: take_pi_args n e
| _ _ := []

namespace interactive
setup_tactic_parser

meta def doneif (h : parse ident?) (t : parse (tk ":" *> texpr))
  (revert : parse (
    (tk "generalizing" *> ((none <$ tk "*") <|> some <$> ident*)) <|> pure (some []))) :
  tactic unit := do
  let h := h.get_or_else `this,
  t ← i_to_expr ``(%%t : Sort*),
  (num_generalized, goal) ← retrieve (do
    assert_core h t, swap,
    num_generalized ← match revert with
    | none := revert_all
    | some revert := revert.mmap tactic.get_local >>= revert_lst
    end,
    goal ← target,
    return (num_generalized, goal)),
  tactic.assert h goal,
  goal ← target,
  (take_pi_args num_generalized goal).reverse.mmap' $ λ h,
    try (tactic.get_local h >>= tactic.clear),
  intron (num_generalized + 1)

meta def wlog (h : parse ident?) (t : parse (tk ":" *> texpr)) : tactic unit :=
doneif h t none >> swap

end interactive
end tactic
