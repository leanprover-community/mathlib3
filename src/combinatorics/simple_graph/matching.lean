/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov.
-/
import data.fintype.basic
import data.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.coloring
import data.fin
/-!
# Matchings


## Main definitions

* a `matching` on a simple graph is a subset of its edge set such that
   no two edges share an endpoint.

* a `perfect_matching` on a simple graph is a matching in which every
   vertex belongs to an edge.

TODO:
  - Lemma stating that the existence of a perfect matching on `G` implies that
    the cardinality of `V` is even (assuming it's finite)
  - Hall's Marriage Theorem
  - Tutte's Theorem
  - consider coercions instead of type definition for `matching`:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532935457
  - consider expressing `matching_verts` as union:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532906131

TODO: Tutte and Hall require a definition of subgraphs.
-/
open finset
universe u

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
structure matching :=
(edges : set (sym2 V))
(sub_edges : edges ⊆ G.edge_set)
(disjoint : ∀ (x y ∈ edges) (v : V), v ∈ x ∧ v ∈ y → x = y)

instance : inhabited (matching G) :=
⟨⟨∅, set.empty_subset _, λ _ _ hx, false.elim (set.not_mem_empty _ hx)⟩⟩

variables {G}

/--
`M.support` is the set of vertices of `G` that are
contained in some edge of matching `M`
-/
def matching.support (M : G.matching) : set V :=
{v : V | ∃ x ∈ M.edges, v ∈ x}

/--
A perfect matching `M` on graph `G` is a matching such that
  every vertex is contained in an edge of `M`.
-/
def matching.is_perfect (M : G.matching) : Prop :=
M.support = set.univ

lemma matching.is_perfect_iff (M : G.matching) :
M.is_perfect ↔ ∀ (v : V), ∃ e ∈ M.edges, v ∈ e :=
set.eq_univ_iff_forall

def bipartite (G : simple_graph V) : Prop :=
  colorable G (fin 2)

section bipartite
variables [bipartite G] (f : G.coloring (fin 2)) (a b : fin 2)

theorem hall_marriage_theorem (a b : fin 2) (h1 : a ≠ b)
[fintype (color_class f a)] [fintype (color_class f b)]
(h2 : (fin_color_class f a).card ≤ (fin_color_class f b).card) :
--∃ (M : G.matching), M.is_perfect ↔ ∀ S ⊆ (set.preimage f.1 _ _),

end bipartite

end simple_graph
