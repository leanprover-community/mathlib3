/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

Bundled types.
-/

/-!
`bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `category` instances for these in `concrete_category.lean` (for categories with unbundled
homs, e.g. topological spaces) and in `bundled_hom.lean` (for categories with bundled homs, e.g.
monoids).
-/

universes u v

namespace category_theory
variables {c d : Type u → Type v} {α : Type u}

/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
structure bundled (c : Type u → Type v) : Type (max (u+1) v) :=
(α : Type u)
(str : c α . tactic.apply_instance)

def mk_ob {c : Type u → Type v} (α : Type u) [str : c α] : bundled c := ⟨α, str⟩

namespace bundled

instance : has_coe_to_sort (bundled c) :=
{ S := Type u, coe := bundled.α }

/-- Map over the bundled structure -/
def map (f : ∀ {α}, c α → d α) (b : bundled c) : bundled d :=
⟨b.α, f b.str⟩

end bundled

end category_theory
