/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin, Reid Barton
-/

import tactic.core
import tactic.dependencies

/-!

# Without loss of generality tactic

The tactic `wlog h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).
The new goal will be placed at the top of the goal stack.
For a version that leaves the main goal on top of the stack, see `doneif`.

-/

namespace tactic

/-- A helper tactic to retrieve the names of the first `n` arguments to a Pi-expression. -/
meta def take_pi_args : nat → expr → list name
| (n+1) (expr.pi h _ _ e) := h :: take_pi_args n e
| _ _ := []

namespace interactive
setup_tactic_parser

/-- `doneif` is a tactic that behaves very similar to `wlog`,
the difference being the order in which goals are placed on the stack
and the amount of context that is reverted by default.

`doneif h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The main goal will remain at the top of the stack.

In the new goal, there will be two assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the name `this` is used, but the idiom `using H` can be added to specify the name:
  `doneif h : P using H`.

Typically, it is useful to use the variant `doneif h : P generalizing x y`,
to revert certain parts of the context before creating the new goal.
In this way, the claim `this` can be applied to `x` and `y` in different orders
(exploiting symmetry, which is the typical use case).

By default, nothing is reverted. -/
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

add_tactic_doc
{ name        := "doneif",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.doneif],
  tags        := ["logic"] }

/-- `wlog h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The new goal will be at the top of the stack. In the new goal, there will be two assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the name `this` is used, but the idiom `using H` can be added to specify the name:
  `wlog h : P using H`.

Typically, it is useful to use the variant `wlog h : P generalizing x y`,
to revert certain parts of the context before creating the new goal.
In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
(exploiting symmetry, which is the typical use case).

By default, the entire context is reverted.

See `doneif` for a version that leaves the main goal at the top of the stack,
and that doesn't revert the entire context by default. -/
meta def wlog (H : parse ident) (t : parse (tk ":" *> texpr))
  (revert : parse (
    (tk "generalizing" *> ((none <$ tk "*") <|> some <$> ident*)) <|> pure none))
  (h : parse (tk "using" *> ident)?) :
  tactic unit :=
doneif H t revert h >> swap

add_tactic_doc
{ name        := "wlog",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.wlog],
  tags        := ["logic"] }

end interactive
end tactic
