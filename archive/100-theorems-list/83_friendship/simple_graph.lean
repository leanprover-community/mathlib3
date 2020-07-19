/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import data.fintype.basic

/-!
# Category of categories
This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.
## Implementation notes
Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/

open_locale classical
open finset
noncomputable theory

universe u

variable (V : Type u)

structure simple_graph :=
(E : V → V → Prop)
(loopless : irreflexive E)
(undirected : symmetric E)

namespace simple_graph
variables {V} (G : simple_graph V)

@[simp] lemma irrefl {v : V} : ¬ G.E v v := G.loopless v

variable [fintype V]

def neighbors (v : V) : finset V := univ.filter (G.E v)

@[simp] lemma neighbor_iff_adjacent (v w : V) :
 w ∈ neighbors G v ↔ G.E v w := by { unfold neighbors, simp }

def degree (v : V) : ℕ := (neighbors G v).card

def regular_graph (d : ℕ) : Prop :=
 ∀ v : V, degree G v = d

lemma edge_symm (u v : V) : G.E u v ↔ G.E v u :=
by split; apply G.undirected

lemma ne_of_edge {a b : V} (hab : G.E a b) : a ≠ b :=
by { intro h, rw h at hab, apply G.loopless b, exact hab }

end simple_graph
