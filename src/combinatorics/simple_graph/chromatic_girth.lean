import combinatorics.simple_graph.coloring

open_locale classical

def simple_graph.girth {V : Type*} [fintype V] : simple_graph V → ℕ := sorry

structure Γ (g n d m : ℕ) :=
(G : simple_graph (fin (n+1)))
(edges_le : G.edge_finset.card = m)
(degree_le : G.max_degree ≤ d * d)
(girth_ge : g ≤ G.girth)

structure Ψ (k n d m : ℕ) :=
(G : simple_graph (fin (n+1)))
(edges_le : G.edge_finset.card = m)
(degree_le : G.max_degree ≤ d * d)
(colourable : G.chromatic_number ≤ k)

def Ψ_ {k n d m : ℕ} (C : fin (n+1) → fin k) :=
{G : Ψ k n d m // ∀ {v w : fin (n+1)}, G.G.adj v w → C v ≠ C w}

a
