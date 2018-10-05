/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

Bundled type and type class instance.
-/

universes u v

/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
structure bundled (c : Sort u → Sort v) : Sort (max (u+1) v) :=
mk' :: (α : Sort u) (inst : c α)

/-
Note on the definition of `bundled`:

It is possible to define `bundled` with square brackets for the instance:

  structure bundled (c : Sort u → Sort v) :=
  (α : Sort u) [inst : c α]

The result is a constructor with this type:

  mk : ∀ (c : Sort u → Sort v) (α : Sort u) [c α], bundled c

However, that leads to needing `@mk` in practice and does not appear to provide
any benefit. Therefore, we defined the constructor as above along with a wrapper
below.
-/

namespace bundled
variables {c d : Sort u → Sort v} {α : Sort u}

/-- A convenient wrapper around `bundled.mk'` with an implicit instance. -/
def mk (α : Sort u) [h : c α] : bundled c :=
mk' α h

instance : has_coe_to_sort (bundled c) :=
{ S := Sort u, coe := bundled.α }

/-- Map over the bundled instance -/
def map (f : ∀ {α}, c α → d α) (b : bundled c) : bundled d :=
mk' b.α (f b.inst)

/- See the following definitions for examples of using `bundled`. -/

/-- Bundled `decidable_eq` -/
@[reducible] def deceq : Sort (max (u+1) u 1) := bundled decidable_eq
instance {d : deceq} : decidable_eq d := d.inst

end bundled
