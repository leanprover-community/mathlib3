/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

/-!
# Changing universes of types in meta-code

This file defines the meta type `uchange (α : Type v) : Type u`, which
permits us to change the universe of a type analogously to `ulift`.
However since `uchange` is meta, it can both lift and lower the universe.

The implementation of `uchange` is efficient. Both `uchange.up` and
`uchange.down` compile to no-ops.
-/

universes u v

/--
`unchecked_cast' a : β` performs an unchecked cast of `(a : α)` to `β`.

Unlike `unchecked_cast`, it can cast across universes. The VM implementation
is guaranteed to be the identity.
-/
@[inline, irreducible]
meta def unchecked_cast' {α : Sort u} {β : Sort v} (a : α) : β :=
plift.down $ @cast (α → β → plift β) (β → α → plift β) undefined (λ _ a, plift.up a)
  (cast undefined punit.star) a

/--
`uchange (α : Sort v) : Sort u` is an equivalent type in a different universe.

In the VM, both `α` and `uchange α` have the same representation.

This definition is `meta` because it collapses the universe hierarchy; if pure code could do
this then one could derive Girard's paradox.
-/
meta def uchange (α : Type v) : Type u :=
unchecked_cast' α

namespace uchange
variables {α : Type v} (a : α)

meta instance [decidable_eq α] : decidable_eq (uchange α) :=
unchecked_cast' (by apply_instance : _root_.decidable_eq α)

/--
`uchange.down` embeds `α` to `uchange α`.

The VM implementation is guaranteed to be the identity.
-/
@[inline]
meta def down {α} (a : α) : uchange α :=
unchecked_cast' a

/--
`uchange.up` extracts from `uchange α` an `α`.

The VM implementation is guaranteed to be the identity.
-/
@[inline]
meta def up {α} (a : uchange α) : α :=
unchecked_cast' a

end uchange

-- Sanity check
#eval do
guard $ (uchange.down.{0} 42).up = 42,
tactic.skip
