/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import tactic.doc_commands

namespace tactic
namespace interactive
open interactive interactive.types expr tactic

/-!
# `specialize'`

`specialize'` is a variant of specialize, the only difference being the order of the goals generated
by any underscores used. That is, `specialize'` puts the goals from the underscores first.
-/

/--
A variant of `specialize` that puts the current goal last. That is, if we have a hypothesis
`h : ∀ x > 0, f x`, then we can use `specialize h x _`, and then we would get two goals. The first
would be the current goal, the second goal is for the underscore.

With `specialize'`, the goal for any underscores comes first, then the current goal.
-/
meta def specialize' (p : parse texpr) : tactic unit :=
do
  n ← list.length <$> get_goals,
  specialize p,
  n' ← list.length <$> get_goals,
  g :: gs ← get_goals,
  set_goals $ gs.take (n' - n) ++ [g] ++ gs.drop (n' - n)

end interactive

add_tactic_doc
{ name                     := "specialize'",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.specialize'],
  tags                     := ["context management", "lemma application"] }
end tactic
