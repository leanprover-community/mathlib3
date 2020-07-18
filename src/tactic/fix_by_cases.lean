/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

/-!
# Fix the `by_cases` tactic

The core `by_cases` tactic has several bugs:
 - It only works if the proposition is decidable.
 - It sometimes unfolds the proposition.

We override the `by_cases` tactic with a correct implementation here.
-/

namespace tactic

/--
Do not use this function directly, use `tactic.by_cases`.
-/
meta def by_cases' (e : expr) (h : name) : tactic unit := do
dec_e ← mk_app ``decidable [e] <|> fail "by_cases tactic failed, type is not a proposition",
inst ← mk_instance dec_e <|> pure `(classical.prop_decidable %%e),
tgt ← target,
expr.sort tgt_u ← infer_type tgt >>= whnf,
g1 ← mk_meta_var (e.imp tgt),
g2 ← mk_meta_var (`(¬ %%e).imp tgt),
focus1 $ do
  exact $ expr.const ``dite [tgt_u] e inst tgt g1 g2,
  set_goals [g1, g2],
  all_goals' $ intro h >> skip

attribute [vm_override by_cases'] by_cases

end tactic
