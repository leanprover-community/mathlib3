/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/

import graph_theory.basic
import data.zmod.basic

/-!
# Strong product of graphs
-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

namespace graph

variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {W : Type*}
variables {G : graph V} {G₁ : graph V₁} {G₂ : graph V₂} {G₃ : graph V₃}

def cyclic (n : ℕ+) : graph (zmod n) :=
{ edge := assume x y, x = y + 1 ∨ y = x + 1,
  symm := assume x y, or.symm }

-- TODO(jmc): Currently a cycle is a function, instead of a subset.
-- There will be multiple cycles with the same image.
-- This is probably bad.

structure cycle (n : ℕ+) (G : graph V) extends hom (cyclic n) G :=
(inj : function.injective to_fun)

end graph
