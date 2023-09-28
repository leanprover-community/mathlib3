import combinatorics.simple_graph.degree_sum

namespace simple_graph
variables {V V' : Type*} {G : simple_graph V} {K K' : Type*}

open fintype (card)
open finset

section

theorem exists_even_degree [fintype V] [decidable_rel G.adj] (hV : odd (card V)) :
  ∃ v : V, even (G.degree v) :=
begin
  have := even_card_odd_degree_vertices G,
  have : univ.filter (λ (v : V), odd (G.degree v)) ≠ univ,
  { rw [←card_lt_iff_ne_univ, lt_iff_le_and_ne],
    refine ⟨card_le_univ _, _⟩,
    intro h,
    rw [h, nat.even_iff_not_odd] at this,
    exact this hV },
  rw [ne.def, filter_eq_self] at this,
  simpa using this
end

end

end simple_graph
