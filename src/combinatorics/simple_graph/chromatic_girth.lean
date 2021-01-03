import combinatorics.simple_graph.coloring
import data.real.basic

open_locale classical big_operators

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
fintype.of_injective Ψ.G Ψ.ext

noncomputable instance {k n d m : ℕ} : fintype (Γ k n d m) :=
fintype.of_injective Γ.G Γ.ext

@[derive fintype]
def Ψ_ (k n d m : ℕ) (C : fin n → fin k) :=
{G : Ψ k n d m // ∀ {v w : fin n}, G.G.adj v w → C v ≠ C w}

lemma edge_bound_of_mem_Ψ_C_aux (k n d m : ℕ) (C : fin n → fin k) (G : Ψ_ k n d m C) :
  (G.1.G.edge_finset.card : ℝ) ≤ n.choose 2 - ∑ (i : fin k), (C ⁻¹' {i}).to_finset.card.choose 2 :=
begin
  sorry
end

lemma edge_bound_of_mem_Ψ_C (k n d m : ℕ) (C : fin n → fin k) (G : Ψ_ k n d m C) :
  (G.1.G.edge_finset.card : ℝ) ≤ 1/2 * n^2 * (1 - 1 / k) :=
begin
  sorry
end

lemma Ψ_C_bound {k n d m : ℕ} (C : fin n → fin k) :
  (fintype.card (Ψ_ k n d m C) : ℝ) ≤ ((1/2 * n^2 * (1 - 1 / k))^m) :=
begin
  sorry
end
