/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import data.finset.pairwise

/-!
# Graph cliques

This file defines cliques in simple graphs. A `n`-clique is a set of `n` vertices which are
pairwise connected.

## Main declarations

* `simple_graph.is_n_clique`: Predicate for a set of vertices to be a `n`-clique.
-/

open finset fintype

namespace simple_graph
variables {α : Type*} (G H : simple_graph α) {n : ℕ} {s : finset α}

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure is_n_clique (n : ℕ) (s : finset α) : Prop :=
(card_eq : s.card = n)
(pairwise : (s : set α).pairwise G.adj)

lemma is_n_clique_iff : G.is_n_clique n s ↔ s.card = n ∧ (s : set α).pairwise G.adj :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

instance [decidable_eq α] [decidable_rel G.adj] {n : ℕ} {s : finset α} :
  decidable (G.is_n_clique n s) :=
decidable_of_iff' _ G.is_n_clique_iff

variables {G H}

lemma is_n_clique.le (h : G ≤ H) : G.is_n_clique n s → H.is_n_clique n s :=
by { simp_rw is_n_clique_iff, exact and.imp_right (set.pairwise.mono' h) }

end simple_graph
