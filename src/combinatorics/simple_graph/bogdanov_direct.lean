import combinatorics.simple_graph.matching

variables {V : Type*} (G : simple_graph V)

namespace simple_graph

def disjoint_perfect_matchings : Prop :=
∀ m₁ m₂ : subgraph G, m₁.is_perfect_matching → m₂.is_perfect_matching →
  disjoint m₁.edge_set m₂.edge_set

variables [fintype V]

lemma thing (black red blue : sym2 V → Prop)
  (a b : V) (Gab : G.adj a b) (bkGab : black ⟦(a, b)⟧) : sorry :=
begin
end

lemma thing (black red blue : sym2 V → Prop)
  (cols_union : ∀ e, black e ∨ red e ∨ blue e)
  (black_red_disj : ∀ e, ¬ (black e ∧ red e))
  (black_blue_disj : ∀ e, ¬ (black e ∧ blue e))
  (red_blue_disj : ∀ e, ¬ (red e ∧ blue e))
  (black_matching : ∀ e₁ e₂ x, black e₁ → black e₂ → x ∈ e₁ → x ∈ e₂ → e₁ = e₂)
  (red_matching : ∀ e₁ e₂ x, red e₁ → red e₂ → x ∈ e₁ → x ∈ e₂ → e₁ = e₂)
  (blue_matching : ∀ e₁ e₂ x, blue e₁ → blue e₂ → x ∈ e₁ → x ∈ e₂ → e₁ = e₂)
  -- (h₁ : G.disjoint_perfect_matchings)
  -- (h₂ : )

-- def k4_perfect_matchings :
--   finset (subgraph (complete_graph (fin 4))) :=
-- { ⟨set.univ, _, _, _⟩ }

-- lemma k4_perfect_matchings :
  -- ∀ m : subgraph G, m.is_perfec(complete_graph (fin 4)).disjoint_perfect_matchings := _

end simple_graph
