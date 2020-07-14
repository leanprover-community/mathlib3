/-
Copyright (c) 2020 Dany Fabian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/

import tactic.split_ifs
namespace tactic

open expr

namespace unfold_cases
meta def find_splitting_expr : expr → tactic expr
| `(@ite %%cond %%dec_inst _ _ _ = _) := pure `(@decidable.em %%cond %%dec_inst)
| `(%%l@(app x y) = _) := pure y
| e := fail!"expected an expression of the form: f x = y. Got:\n{e}"

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
  This tactic unfolds the definition of a function or pattern match expression.
  Then it introduces recursively introduces a distinction by cases. The decision what express
  to do the distinction on is driven by the pattern match expression.

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
