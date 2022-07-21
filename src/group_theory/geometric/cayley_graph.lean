/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgi Kocharyan
-/
import combinatorics.simple_graph.metric
import group_theory.geometric.marked_group

/-!
# Cayley graphs
-/

namespace geometric_group_theory
variables {G S : Type*} [group G] (m : marking G S)

def cayley : simple_graph G := simple_graph.from_rel $ λ g h, ∃ s : S, g * m (free_group.of s) = h

lemma cayley_preconnected : (cayley m).preconnected :=
begin
  intros x y,
  sorry,
end

lemma cayley_connected [nonempty G] : (cayley m).connected := ⟨cayley_preconnected _⟩

variables (g : G)

lemma dist_cayley (g h : G) : ((cayley m).dist g h : ℝ) = dist (to_marked g : marked m) h := sorry

end geometric_group_theory
