/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

Bundled type and type class instance.
-/

universes u v

/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
structure bundled (c : Type u → Type v) : Type (max (u+1) v) :=
(α : Type u)
(inst : c α)

/-
Note on the definition of `bundled`:

It is possible to define `bundled` with square brackets for the instance:

  structure bundled (c : Type u → Type v) :=
  (α : Type u)
  [inst : c α]

The result is a constructor with this type:

  mk : ∀ (c : Type u → Type v) (α : Type u) [c α], bundled c

However, that leads to needing `@mk` in practice and does not appear to provide
any benefit. Therefore, we defined the constructor without square brackets.
-/

namespace bundled
variables {c d : Type u → Type v} {α : Type u}

instance : has_coe_to_sort (bundled c) :=
{ S := Type u, coe := bundled.α }

/-- Map over the bundled instance -/
def map (f : ∀ {α}, c α → d α) (b : bundled c) : bundled d :=
⟨b.α, f b.inst⟩

end bundled
