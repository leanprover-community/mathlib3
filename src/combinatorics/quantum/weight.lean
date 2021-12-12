/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import combinatorics.weighted_graph.matching

/-!
# Weighted graphs
-/

variables {α W : Type*}

namespace weighted_graph
section monoid
variables [monoid W] {G : weighted_graph α W}

/-- The product of the weights of the edges of a subgraph. -/
def subgraph.prod_weight (G' : G.subgraph) : W :=
begin

end

end monoid

section semiring
variables [semiring W] (G : weighted_graph α W)

/-- -/
def monochromatic : Prop :=

def col : ℕ :=
sorry

end semiring

section canonically_ordered_comm_semiring
variables [fintype α] [canonically_ordered_comm_semiring W] (G : weighted_graph α W)

lemma canon_bogdanov2 (hα : 5 ≤ fintype.card α) : col ≤ 2 := sorry

lemma canon_bogdanov3 : col ≤ 3 := sorry

end canonically_ordered_comm_semiring
end weighted_graph
