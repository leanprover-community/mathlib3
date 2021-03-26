/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.continuous_function.bounded

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so gain various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some, but not all of the lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`bounded_continuous_function.equiv_continuous_map_of_compact` to functions back and forth.

-/

noncomputable theory
open_locale topological_space classical nnreal

open set filter metric

namespace continuous_map

end continuous_map
