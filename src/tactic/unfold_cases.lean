/-
Copyright (c) 2020 Dany Fabian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/

import tactic.split_ifs
namespace tactic

open expr
/-!
  # Unfold cases tactic

  In Lean, pattern matching expressions are not atomic parts of the syntax, but
  rather they are compiled down into simpler terms that are later checked by the kernel.

  This allows Lean to have a minimalistic kernel but can occasionally lead an explosion
  of cases that need to be considered. What looks like one case in the `match` expression
  can in fact be compiled into many different cases that all need to proved by case analysis.

  This tactic automates the process by allowing us to write down an equation `f x = y`
  where we know that `f x = y` is provably true, but does not hold definitionally. In that
  case the `unfold_cases` tactic will continue unfolding `f` and introducing `cases` where
  necessary until the left hand side becomes definitionally equal to the right hand side.
-/
namespace unfold_cases
/--
  Given an equation `f x = y`, this tactic tries to infer an expression that can be
  used to do distinction by cases on to make progress.

  Pre-condition: assumes that the outer-most application cannot be beta-reduced
  (e.g. `whnf` or `dsimp`).
-/
meta def find_splitting_expr : expr → tactic expr
| `(@ite %%cond %%dec_inst _ _ _ = _) := pure `(@decidable.em %%cond %%dec_inst)
| `(%%l@(app x y) = _) := pure y
| e := fail!"expected an expression of the form: f x = y. Got:\n{e}"

/--
  Tries to finish the current goal using the `inner` tactic. If the tactic
  fails, it tries to find an expression on which to do a distinction by
  cases and calls itself recursively.

  The order of operations is significant. Because the unfolding can potentially
  be infinite, it is important to apply the `inner` tactic at every step.

  Notice, that if the `inner` tactic succeeds, the recursive unfolding is stopped.
-/
meta def unfold_cases_core (inner : interactive.itactic) : tactic unit :=
inner <|>
(do split_ifs [], all_goals unfold_cases_core, skip) <|>
do
  tgt ← target,
  e ← find_splitting_expr tgt,
  focus1 $ do
    cases e,
    all_goals $ (dsimp_target >> unfold_cases_core) <|> skip,
    skip

/--
  Given a target of the form `⊢ f x₁ ... xₙ = y`, unfolds `f` using a delta reduction.
-/
meta def unfold_tgt : expr → tactic unit
| e@`(%%l@(app _ _) = %%r) :=
  match l.get_app_fn with
  | const n ls := delta_target [n]
  | e := fail!"couldn't unfold:\n{e}"
  end
| e := fail!"expected an expression of the form: f x = y. Got:\n{e}"
end unfold_cases

namespace interactive
open unfold_cases

/--
  This tactic unfolds the definition of a function or `match` expression.
  Then it recursively introduces a distinction by cases. The decision what expression
  to do the distinction on is driven by the pattern matching expression.

  A typical use case is using `unfold_cases { refl }` to collapse cases that need to be
  considered in a pattern matching.

  ```lean
  have h : foo x = y, by unfold_cases { refl },
  rw h,
  ```

  The tactic expects a goal in the form of an equation, possibly universally quantified.

  Further examples can be found in `test/unfold_cases.lean`.
-/
meta def unfold_cases (inner : itactic) : tactic unit := focus1 $ do
  tactic.intros,
  tgt ← target,
  unfold_tgt tgt,
  try dsimp_target,
  unfold_cases_core inner

add_tactic_doc
{ name       := "unfold_cases",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.unfold_cases],
  tags       := ["induction"] }

end interactive
end tactic
