/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.doc_commands
/-!
# Instance cache tactics

For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics in this file
helps to force such updates.

-/

open tactic.interactive

/--
For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics described below
helps to force such updates. For a simple (but very artificial) example,
consider the function `default` from the core library. It has type
`Π (α : Sort u) [inhabited α], α`, so one can use `default` only if Lean
can find a registered instance of `inhabited α`. Because the database of
such instance is not automatically updated during a proof, the following
attempt won't work (Lean will not pick up the instance from the local
context):
```lean
def my_id (α : Type) : α → α :=
begin
  intro x,
  have : inhabited α := ⟨x⟩,
  exact default, -- Won't work!
end
```
However, it will work, producing the identity function, if one replaces `have`
by its variant `haveI` described below.

* `resetI`: Reset the instance cache. This allows any instances
  currently in the context to be used in typeclass inference.

* `unfreezingI { tac }`: Unfreeze local instances while executing the tactic `tac`.

* `introI`/`introsI`: `intro`/`intros` followed by `resetI`. Like
  `intro`/`intros`, but uses the introduced variable in typeclass inference.

* `casesI`: like `cases`, but can also be used with instance arguments.

* `substI`: like `subst`, but can also substitute in type-class arguments

* `haveI`/`letI`/`rsufficesI`: `have`/`let`/`rsuffices` followed by `resetI`. Used
  to add typeclasses to the context so that they can be used in typeclass inference.

* `exactI`: `resetI` followed by `exact`. Like `exact`, but uses all
  variables in the context for typeclass inference.
-/
add_tactic_doc
{ name        := "Instance cache tactics",
  category    := doc_category.tactic,
  decl_names  := [``resetI, ``unfreezingI, ``casesI, ``substI, ``introI, ``introsI, ``haveI, ``letI,
                  ``exactI],
  tags        := ["type class", "context management"] }
