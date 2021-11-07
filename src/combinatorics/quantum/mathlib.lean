/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.subgraph

/-!
# Stuff that belongs in mathlib
-/

open set

variables {α : Type*} {G : simple_graph α}

namespace simple_graph
variables {a : α}

lemma neighbor_set_bot (a : α) : (⊥ : simple_graph α).neighbor_set a = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x, id

instance simple_graph.bot.locally_finite : locally_finite (⊥ : simple_graph α) :=
λ a, ⟨∅, λ x, neighbor_set_bot x ▸ x.2⟩


namespace subgraph


end subgraph
end simple_graph
