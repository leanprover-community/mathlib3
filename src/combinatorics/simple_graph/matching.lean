/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov.
-/
import data.fintype.basic
import data.sym2
import combinatorics.simple_graph.basic
/-!
# Matchings


## Main definitions

* a `matching` on a simple graph is a subset of its edge set such that
   no two edges shares an endpoint.

* a `perfect_matching` on a simple graph is a matching in which every
   vertex belongs to an edge.

## Implementation notes


TODO: perfect matchings, Hall's Marriage Theorem

-/
open finset
universe u

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
A matching on `G` is a subset of its edges such that no two edges share an endpoint.
-/
def matching (M : set (sym2 V)) (h : M ⊆ edge_set G) : Prop :=
  ∀ x y ∈ M, ∀ v : V, v ∈ x ∧ v ∈ y → x = y

/--
A perfect matching on `G` is a matching such that every vertex is contained in an edge.
-/
def perfect_matching (P : set (sym2 V)) (h1 : P ⊆ edge_set G) (h2 : matching G P h1) :
  Prop := ∀ v : V, ∃ x ∈ P, v ∈ x

end simple_graph
