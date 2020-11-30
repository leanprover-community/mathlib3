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

TODO:
  - Lemma stating that the existence of a perfect matching on `G` implies that
    the cardinality of `V` is even (assuming it's finite)
  - Hall's Marriage Theorem
  - Tutte's Theorem

TODO: Tutte and Hall require a definition of subgraphs.
-/
open finset
universe u

namespace simple_graph
variables {V : Type u} (G : simple_graph V) (M : set (sym2 V)) (h : M ⊆ edge_set G)

instance : inhabited (set (sym2 V)) :=
  { default := (complete_graph V).edge_set }

/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
def matching : Type* :=
  { M : set (sym2 V) // M ⊆ edge_set G ∧ ∀ x ∈ M, ∀ y ∈ M, ∀ v : V, v ∈ x ∧ v ∈ y → x = y }

instance : inhabited (matching G) := { default :=
  ⟨(∅ : set (sym2 V)),
    begin
      split,
      exact set.empty_subset G.edge_set,
      intros x hx y hy v hv,
      have h2 := set.mem_empty_eq x,
      by_contra,
      rw ← h2,
      exact hx,
    end ⟩ }

/--
A perfect matching on `G` with vertex set `V` is a matching such that
  every vertex in `V` is contained in an edge of `G`.
-/
def perfect_matching (M : matching G) :
  Prop := ∀ v : V, ∃ x ∈ M.1, v ∈ x

end simple_graph
