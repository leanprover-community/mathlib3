/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Johan Commelin, Reid Barton
-/

import tactic.core
import tactic.dependencies

/-!

# Without loss of generality tactic

The tactic `wlog h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).
The new goal will be placed at the top of the goal stack.

-/

namespace tactic

/-- A helper function to retrieve the names of the first `n` arguments to a Pi-expression. -/
meta def take_pi_args : nat → expr → list name
| (n+1) (expr.pi h _ _ e) := h :: take_pi_args n e
| _ _ := []

namespace interactive
setup_tactic_parser

/-- `wlog h : P` will add an assumption `h : P` to the main goal,
and add a side goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The side goal will be at the top of the stack. In this side goal, there will be two assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the name `this` is used, but the idiom `with H` can be added to specify the name:
  `wlog h : P with H`.

Typically, it is useful to use the variant `wlog h : P generalizing x y`,
to revert certain parts of the context before creating the new goal.
In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
(exploiting symmetry, which is the typical use case).

By default, the entire context is reverted. -/
meta def wlog (H : parse ident) (t : parse (tk ":" *> texpr))
  (revert : parse ((tk "generalizing" *> ((none <$ tk "*") <|> some <$> ident*)) <|> pure none))
  (h : parse (tk "with" *> ident)?) :
  tactic unit := do
  -- if there is no `with` clause, use `this` as default name
  let h := h.get_or_else `this,
  t ← i_to_expr ``(%%t : Sort*),
  -- compute which constants must be reverted (by default: everything)
  (num_generalized, goal, rctx) ← retrieve (do
    assert_core H t, swap,
    -- use `revert_lst'` to ensure that the order of local constants in the context is preserved
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
  -- prove the easy branch of the side goal
  swap,
  tactic.by_cases t H,
  H ← tactic.get_local H,
  let L := ctx.filter (λ n, n ∉ rctx),
  tactic.exact $ (e.mk_app L).app H

add_tactic_doc
{ name        := "wlog",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.wlog],
  tags        := ["logic"] }

end interactive

end tactic
