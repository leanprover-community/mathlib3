import combinatorics.simple_graph.coloring

open_locale classical

def simple_graph.girth {V : Type*} [fintype V] : simple_graph V → ℕ := sorry

@[ext]
structure Γ (g n d m : ℕ) :=
(G : simple_graph (fin n))
(edges_eq : G.edge_finset.card = m)
(edges_le : G.edge_finset.card ≤ n * d)
(degree_le : ∀ v, G.degree v ≤ d * d)
(girth_ge : g ≤ G.girth)

@[ext]
structure Ψ (k n d m : ℕ) :=
(G : simple_graph (fin n))
(edges_eq : G.edge_finset.card = m)
(edges_le : G.edge_finset.card ≤ n * d)
(degree_le : ∀ v, G.degree v ≤ d * d)
(colourable : G.chromatic_number ≤ k)

noncomputable instance {k n d m : ℕ} : fintype (Ψ k n d m) :=
begin
  apply fintype.of_injective Ψ.G,
  apply Ψ.ext,
  sorry,
end

@[derive fintype]
def Ψ_ (k n d m : ℕ) (C : fin n → fin k) :=
{G : Ψ k n d m // ∀ {v w : fin n}, G.G.adj v w → C v ≠ C w}

lemma Ψ_C_bound {k n d m : ℕ} (C : fin n → fin k) :
  fintype.card (Ψ_ k n d m C) ≤ sorry :=
begin
end
