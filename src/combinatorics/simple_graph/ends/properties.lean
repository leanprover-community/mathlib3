/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import combinatorics.simple_graph.ends.defs
/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/

variables {V : Type} (G : simple_graph V)

namespace simple_graph

lemma ends_of_finite [finite V] : is_empty G.end :=
begin
  rw is_empty_iff,
  rintro ⟨s, sec⟩,
  let K : finset V := set.finite_univ.to_finset,
  obtain ⟨v, h⟩ := (s K).nonempty,
  exact set.disjoint_iff.mp (s K).disjoint_right ⟨by simp only [set.finite.coe_to_finset], h⟩,
end

end simple_graph
