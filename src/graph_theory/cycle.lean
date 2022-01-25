/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/

import data.zmod.basic
import graph_theory.basic

/-!
# Cyclic graphs
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

namespace cycle

instance (n : ℕ+) (G : graph V) : has_coe_to_fun (G.cycle n) :=
{ F := λ c, zmod n → V,
  coe := λ c, c.to_fun }

@[ext]
lemma ext {n : ℕ+} (c₁ c₂ : G.cycle n) (h : (c₁ : zmod n → V) = c₂) :
  c₁ = c₂ :=
by { cases c₁, cases c₂, congr, apply graph.hom.ext, exact h }

end cycle

end graph
