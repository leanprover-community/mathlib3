/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.rat.defs
import logic.encodable.basic

/-! # The rationals are `encodable`.

As a consequence we also get the instance `countable ℚ`.

This is kept separate from `data.rat.defs` in order to minimize imports.
-/

namespace rat

instance : encodable ℚ := encodable.of_equiv (Σ n : ℤ, {d : ℕ // 0 < d ∧ n.nat_abs.coprime d})
  ⟨λ ⟨a, b, c, d⟩, ⟨a, b, c, d⟩, λ⟨a, b, c, d⟩, ⟨a, b, c, d⟩,
   λ ⟨a, b, c, d⟩, rfl, λ⟨a, b, c, d⟩, rfl⟩

end rat
