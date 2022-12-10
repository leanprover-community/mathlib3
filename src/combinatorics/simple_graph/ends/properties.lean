/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import combinatorics.simple_graph.ends.defs

universes u
variables {V : Type u} (G : simple_graph V)

namespace simple_graph

lemma ends_of_fintype [finite V] : is_empty G.end :=
begin
  rw is_empty_iff,
  rintro ⟨s, sec⟩,
  let K : finset V := set.finite_univ.to_finset,
  obtain ⟨v, h⟩ := (s K).nempty,
  exact set.disjoint_iff.mp (s K).outside ⟨by simp only [set.finite.coe_to_finset], h⟩,
end

end simple_graph
