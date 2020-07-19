/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2

/-!
# Simple graphs
This file contains a definition of simple graphs,
together with a basic API for graphs with a fintype of vertices.

## Implementation notes
We give essentially the simplest notion of graph.
This is bad in the sense that it starts at the "top of the combinatorics hierarchy".
We make this tradeoff in order to start learning what the combinatorics hierarchy should look like.
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

def E : Type u := { x : sym2 V // x ∈ sym2.from_rel G.sym }

@[simp] lemma irrefl {v : V} : ¬ G.adj v v := G.loopless v

variable [fintype V]

instance : fintype (G.E) := subtype.fintype (λ x, x ∈ sym2.from_rel G.sym)

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
