/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import combinatorics.simple_graph.basic_mathlib
import combinatorics.simple_graph.clique

/-!
# Stuff for combinatorics.simple_graph.clique
-/

namespace simple_graph

variables {V W : Type*} {G : simple_graph V} {H : simple_graph W} {n : ℕ}

lemma not_clique_free_iff' (n : ℕ) :
  ¬ G.clique_free n ↔ nonempty ((⊤ : simple_graph (fin n)) →g G) :=
by rw [not_clique_free_iff, (simple_graph.top_hom_graph_equiv).nonempty_congr]

lemma clique_free_iff' {n : ℕ} :
  G.clique_free n ↔ is_empty ((⊤ : simple_graph (fin n)) →g G) :=
by rw [← not_iff_not, not_clique_free_iff', not_is_empty_iff]

lemma clique_free.hom (f : G →g H) : H.clique_free n → G.clique_free n :=
λ h, clique_free_iff'.2 ⟨λ x, (clique_free_iff'.1 h).elim' (f.comp x)⟩

end simple_graph
