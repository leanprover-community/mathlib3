/-
Copyright (c) 2022 Joanna Choules. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joanna Choules
-/
import topology.category.Top.limits
import combinatorics.simple_graph.subgraph

/-!
# Homomorphisms from finite subgraphs

This file defines the type of finite subgraphs of a `simple_graph`.

## Notations

`→fg` is a module-local variant on `→g` where the domain is a finite subgraph of some supergraph
`G`.
-/

universes u v
variables {V : Type u} {W : Type v} {G : simple_graph V} {F : simple_graph W}

namespace simple_graph

/-- The subtype of `G.subgraph` comprising those subgraphs with finite vertex sets. -/
abbreviation finsubgraph (G : simple_graph V) := { G' : G.subgraph // G'.verts.finite }

/-- A graph homomorphism from a finite subgraph of G to F. -/
abbreviation finsubgraph_hom (G' : G.finsubgraph) (F : simple_graph W) := G'.val.coe →g F

local infix ` →fg ` : 50 := finsubgraph_hom

/-- The finite subgraph of G generated by a single vertex. -/
def singleton_finsubgraph (v : V) : G.finsubgraph := ⟨simple_graph.singleton_subgraph _ v, by simp⟩

/-- The finite subgraph of G generated by a single edge. -/
def finsubgraph_of_adj {u v : V} (e : G.adj u v) : G.finsubgraph :=
⟨simple_graph.subgraph_of_adj _ e, by simp⟩

/- Lemmas establishing the ordering between edge- and vertex-generated subgraphs. -/

lemma singleton_finsubgraph_le_adj_left {u v : V} {e : G.adj u v} :
  singleton_finsubgraph u ≤ finsubgraph_of_adj e :=
by simp [singleton_finsubgraph, finsubgraph_of_adj]

lemma singleton_finsubgraph_le_adj_right {u v : V} {e : G.adj u v} :
  singleton_finsubgraph v ≤ finsubgraph_of_adj e :=
by simp [singleton_finsubgraph, finsubgraph_of_adj]

end simple_graph
