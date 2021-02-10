/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import tactic.doc_commands

/-!
# `specialize'`

`specialize'` is a variant of `specialize`, the only difference being the order of the goals generated
by any underscores used. That is, `specialize'` puts the goals from the underscores first.
-/

namespace tactic
namespace interactive
open interactive interactive.types expr tactic

/--
A variant of `specialize` that puts the current goal last. That is, if we have a hypothesis
`h : ∀ x > 0, f x`, then we can use `specialize h x _`, and then we would get two goals. The first
would be the current goal, the second goal is for the underscore.

With `specialize'`, the goal for any underscores comes first, then the current goal.
-/
meta def specialize' (p : parse texpr) : tactic unit :=
do
  g :: gs ← get_goals,
  set_goals [g],
  specialize p,
  g' :: gs' ← get_goals,
  set_goals $ gs' ++ [g'] ++ gs

end interactive

add_tactic_doc
{ name                     := "specialize'",
  category                 := doc_category.tactic,
  decl_names               := [`tactic.interactive.specialize'],
  tags                     := ["context management", "lemma application"] }
end tactic
