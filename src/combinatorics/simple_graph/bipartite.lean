/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.basic

/-!
# Bipartite graphs

This module defines bipartite graphs, which are graphs whose vertices
can be split in two groups such that each group doesn't contain any
pair of adjacent vertices.

## Main definitions

* `G.is_bipartition L R` is the proposition for the sets of vertices `L` and `R` to form
  a bipartition of `G`. They must be complementary w.r.t. `V` and there must be no edges
  in any of them.

* `G.is_bipartite` is the proposition for a graph to be a bipartite graph, that is, there
  must exist two sets of its vertices that form a bipartition.
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- Whether a pair of sets of vertices is a bipartition of `G` or not. -/
def is_bipartition (L R : set V) : Prop :=
(L = set.compl R) ∧
(∀ (v w ∈ L), ¬ G.adj v w) ∧
(∀ (v w ∈ R), ¬ G.adj v w)

/-- Whether `G` is a bipartite graph or not. -/
def is_bipartite : Prop := ∃ (L R : set V), G.is_bipartition L R

/--
Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Bipartite graphs in general may be regarded as being subgraphs of one of these.

TODO maybe replace with complete multi-partite graphs, where the vertex type
is a sigma type of an indexed family of vertex types?
-/
@[simps]
def complete_bipartite_graph (V W : Type*) : simple_graph (V ⊕ W) :=
{ adj := λ v w, (v.is_left ∧ w.is_right) ∨ (v.is_right ∧ w.is_left),
  -- maybe replace adj with v.is_left ↔ ¬w.is_left?
  symm := begin
    intros v w,
    cases v; cases w; simp,
  end,
  loopless := begin
    intro v,
    cases v; simp,
  end }

lemma complete_bipartite_graph_is_bipartite {V W : Type*} (Z := complete_bipartite_graph V W) :
  Z.is_bipartite :=
begin
  rw is_bipartite,
  let L := {v : V ⊕ W | v.is_left},
  let R := {v : V ⊕ W | v.is_right},
  use [L, R],
  rw is_bipartition,
  split,
  { rw set.subset.antisymm_iff,
    split,
    { sorry, },
    { sorry, }, },
  { split,
    { intros v w hv hw,
      sorry, },
    { intros v w hv hw,
      sorry, }, },
end

end simple_graph
