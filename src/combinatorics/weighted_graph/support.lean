/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.weighted_graph.order

/-!
# Support of a weighted graph
-/

variables {α W : Type*}

namespace weighted_graph
variables (G : weighted_graph α W) {a b : α}

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : set α := rel.dom G.adj

lemma mem_support : a ∈ G.support ↔ ∃ b, G.adj a b := iff.rfl

open_locale label_graph

lemma label.support_mono {G₁ G₂ : weighted_graph α W} (h : G₁ ≤ G₂) : G₁.support ⊆ G₂.support :=
rel.dom_mono $ λ a b, label.adj_mono h

end weighted_graph
