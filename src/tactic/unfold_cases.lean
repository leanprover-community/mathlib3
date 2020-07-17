/-
Copyright (c) 2020 Dany Fabian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/

import tactic.split_ifs
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

  Consider a definition as follows:

  ```lean
  def myand : bool → bool → bool
  | ff _ := ff
  | _ ff := ff
  | _ _ := tt
  ```

  The equation compiler generates 4 equation lemmas for us:
  ```lean
  myand ff ff = ff
  myand ff tt = ff
  myand tt ff = ff
  myand tt tt = tt
  ```

  This is not in line with what one might expect looking at the definition.
  Whilst it is provably true, that `∀ x, myand ff x = ff` and `∀ x, myand x ff = ff`,
  we do not get these stronger lemmas from the compiler for free but must in fact
  prove them using `cases` or some other local reasoning.

  In other words, the following does not constitute a proof that lean accepts.
  ```lean
  example : ∀ x, myand ff x = ff :=
  begin
    intros, refl
  end
  ```

  However, you can use `unfold_cases { refl }` to prove `∀ x, myand ff x = ff` and
  `∀ x, myand x ff = ff`. For definitions with many cases, the savings can be very
  significant.

  The term that gets generated for the above definition looks like this:
  ```lean
  λ (a a_1 : bool),
  a.cases_on
    (a_1.cases_on (id_rhs bool ff) (id_rhs bool ff))
    (a_1.cases_on (id_rhs bool ff) (id_rhs bool tt))
  ```

  When the tactic tries to prove the goal `∀ x, myand ff x = ff`, it starts by `intros`,
  followed by unfolding the definition:
  ```lean
  ⊢ ff.cases_on
    (x.cases_on (id_rhs bool ff) (id_rhs bool ff))
    (x.cases_on (id_rhs bool ff) (id_rhs bool tt)) = ff
  ```

  At this point, it can make progress using `dsimp`. But then it gets stuck:
  ```lean
  ⊢ bool.rec (id_rhs bool ff) (id_rhs bool ff) x = ff
  ```

  Next, it can introduce a case split on `x`. At this point, it has to prove two
  goals:
  ```lean
  ⊢ bool.rec (id_rhs bool ff) (id_rhs bool ff) ff = ff
  ⊢ bool.rec (id_rhs bool ff) (id_rhs bool ff) tt = ff
  ```

  Now, however, both goals can be discharged using `refl`.
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
