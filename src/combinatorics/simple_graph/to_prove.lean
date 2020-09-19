import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
open finset

namespace simple_graph

section bollobas

open_locale classical

/-!
Some formalizations of statements from Bollobas, "Modern graph theory"
-/

/--
Veblen 1912 (theorem 1 in book). Every vertex has even degree iff there is a
partition of the graph into edge-disjoint cycles.
-/
theorem edge_partition_cycles (G : simple_graph) [fintype (V G)] :
  (∀ v : V G, degree v % 2 = 0) ↔ (∃ partition : set (subgraph G), (∀ G' ∈ partition, subgraph.is_cycle G') ∧
                                     ∀ (e ∈ G.edge_set), !∃ (c : subgraph G), c ∈ partition ∧
                                       e ∈ c.edge_set') :=
sorry

/--
Mantel 1907 (theorem 2 in book). If a graph with n vertices and m edges satisfies
floor(n^2 /4) < m, then it contains a triangle.
-/
theorem has_triangle (G : simple_graph) [fintype (V G)] (h : (fintype.card (V G))^2 / 4 < G.edge_finset.card) :
  nonempty {f : ↟(cycle_graph 3 (by linarith)) →g G // function.injective f} :=
sorry

end bollobas

end simple_graph
