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
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
/-- Reset the instance cache for the main goal. -/
meta def reset_instance_cache : tactic unit := do
unfreeze_local_instances,
freeze_local_instances

/-- Unfreeze local instances, if the passed expression is amongst the frozen instances. -/
meta def unfreeze (h : expr) : tactic unit :=
do frozen ← frozen_local_instances,
   if h ∈ frozen.get_or_else [] then unfreeze_local_instances else skip

namespace interactive
open interactive interactive.types

/--
**Please use `unfreezingI` instead.**

Unfreeze local instances, which allows us to revert instances in the context.
This command has significant negative peformance implications:
it disables the type-class cache until you call `freezeI` again (the freeze setting is per-goal).
-/
meta def unfreezeI := tactic.unfreeze_local_instances

/--
Freezes the local instances after `unfreezeI`, re-enabling the type-class cache.
-/
meta def freezeI := tactic.freeze_local_instances

/--
`unfreezingI { tac }` executes tac while temporarily unfreezing the instance cache.
-/
meta def unfreezingI (tac : itactic) :=
unfreezeI >> ((show tactic unit, from tac); freezeI)

/-- Reset the instance cache. This allows any new instances
added to the context to be used in typeclass inference. -/
meta def resetI := reset_instance_cache

/-- Like `intro`, but uses the introduced variable
in typeclass inference. -/
meta def introI (p : parse ident_?) : tactic unit :=
intro p >> reset_instance_cache

/-- Like `intros`, but uses the introduced variable(s)
in typeclass inference. -/
meta def introsI (p : parse ident_*) : tactic unit :=
intros p >> reset_instance_cache

/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `have`,
but the proof-omitted version is not supported. For
this one must write `have : t, { <proof> }, resetI, <proof>`. -/
meta def haveI (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse (tk ":=" *> texpr)) :
  tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «have» (some h) q₁ (some q₂),
  match q₁ with
  | none    := swap >> reset_instance_cache >> swap
  | some p₂ := reset_instance_cache
  end

/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `let`. -/
meta def letI (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) :
  tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «let» (some h) q₁ q₂,
  match q₂ with
  | none    := swap >> reset_instance_cache >> swap
  | some p₂ := reset_instance_cache
  end

/-- Like `exact`, but uses all variables in the context
for typeclass inference. -/
meta def exactI (q : parse texpr) : tactic unit :=
reset_instance_cache >> exact q

/--
For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics described below
helps to force such updates. For a simple (but very artificial) example,
consider the function `default` from the core library. It has type
`Π (α : Sort u) [inhabited α], α`, so one can use `default α` only if Lean
can find a registered instance of `inhabited α`. Because the database of
such instance is not automatically updated during a proof, the following
attempt won't work (Lean will not pick up the instance from the local
context):
```lean
def my_id (α : Type) : α → α :=
begin
  intro x,
  have : inhabited α := ⟨x⟩,
  exact default α, -- Won't work!
end
```
However, it will work, producing the identity function, if one replaces `have`
by its variant `haveI` described below.

* `resetI`: Reset the instance cache. This allows any instances
  currently in the context to be used in typeclass inference.

* `unfreezeI`: Unfreeze local instances, which allows us to revert
  instances in the context

* `unfreezingI { tac }`: Unfreeze local instances while executing the tactic `tac`.

* `freezeI`: Freezes the local instances again, which re-enables the type-class cache

* `introI`/`introsI`: `intro`/`intros` followed by `resetI`. Like
  `intro`/`intros`, but uses the introduced variable in typeclass inference.

* `haveI`/`letI`: `have`/`let` followed by `resetI`. Used to add typeclasses
  to the context so that they can be used in typeclass inference. The syntax
  `haveI := <proof>` and `haveI : t := <proof>` is supported, but
  `haveI : t, from _` and `haveI : t, { <proof> }` are not; in these cases
  use `have : t, { <proof> }, resetI` directly.

* `exactI`: `resetI` followed by `exact`. Like `exact`, but uses all
  variables in the context for typeclass inference.
-/
add_tactic_doc
{ name        := "Instance cache tactics",
  category    := doc_category.tactic,
  decl_names  := [``unfreezeI, ``freezeI, ``resetI, ``introI, ``introsI, ``haveI, ``letI, ``exactI],
  tags        := ["type class", "context management"] }

end interactive
end tactic
