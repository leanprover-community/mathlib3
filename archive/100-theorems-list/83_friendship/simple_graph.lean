/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2

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
(adj : V → V → Prop)
(sym : symmetric adj)
(loopless : irreflexive adj)

namespace simple_graph
variables {V} (G : simple_graph V)

/--
The edge set of a simple graph consists of all the unordered pairs
that satisfy the adjacency relation.
-/
def E : set (sym2 V) :=
sym2.from_rel (sym G)

@[simp] lemma irrefl {v : V} : ¬ G.adj v v := G.loopless v

variable [fintype V]

def neighbors (v : V) : finset V := univ.filter (G.adj v)

@[simp] lemma neighbor_iff_adjacent (v w : V) :
 w ∈ neighbors G v ↔ G.adj v w := by { unfold neighbors, simp }

def degree (v : V) : ℕ := (neighbors G v).card

def regular_graph (d : ℕ) : Prop :=
 ∀ v : V, degree G v = d

lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u :=
by split; apply G.sym

lemma ne_of_edge {a b : V} (hab : G.adj a b) : a ≠ b :=
by { intro h, rw h at hab, apply G.loopless b, exact hab }

end simple_graph
