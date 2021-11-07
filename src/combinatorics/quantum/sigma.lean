/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# Graphs over sigma types
-/

variables {ι : Type*} {α : ι → Type*}

namespace simple_graph
variables (k : ℕ) (G : Π i, simple_graph (α i))

inductive eq (α : Type*) : α → α → Prop
| refl (a : α) : eq a a

inductive sigma_adj (G : Π i, simple_graph (α i)) : Σ i, α i → Σ i, α i → Prop
| adj {i : ι} {a b : α i} (h : (G i).adj a b) : sigma_adj (i, a) (i, b)

protected def sigma (G : Π i, simple_graph (α i)) : simple_graph (Σ i, α i) :=
{ adj := simple_graph.sigma_adj G,
  symm := _,
  loopless := _ }

end simple_graph
