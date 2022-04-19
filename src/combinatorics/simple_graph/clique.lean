/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import data.finset.pairwise

/-!
# Graph cliques

This file defines cliques in simple graphs. A clique is a set of vertices which are pairwise
connected.

## Main declarations

* `simple_graph.is_clique`: Predicate for a set of vertices to be a clique.
* `simple_graph.is_n_clique`: Predicate for a set of vertices to be a `n`-clique.

## Todo

* Clique numbers
* Going back and forth between cliques and complete subgraphs or embeddings of complete graphs.
-/

open finset fintype

namespace simple_graph
variables {α : Type*} (G H : simple_graph α)

section clique
variables {s t : set α}

/-- A clique in a graph is a set of vertices which are pairwise connected. -/
structure is_clique (s : set α) : Prop :=
(pairwise : s.pairwise G.adj)

lemma is_clique_iff : G.is_clique s ↔ s.pairwise G.adj := ⟨λ h, h.pairwise, λ h, ⟨h⟩⟩

instance [decidable_eq α] [decidable_rel G.adj] {s : finset α} : decidable (G.is_clique s) :=
decidable_of_iff' _ G.is_clique_iff

variables {G H}

lemma is_clique.mono (h : G ≤ H) : G.is_clique s → H.is_clique s :=
by { simp_rw is_clique_iff, exact set.pairwise.mono' h }

lemma is_clique.subset (h : t ⊆ s) : G.is_clique s → G.is_clique t :=
by { simp_rw is_clique_iff, exact set.pairwise.mono h }

end clique

variables {n : ℕ} {s : finset α}

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure is_n_clique (n : ℕ) (s : finset α) extends is_clique G s : Prop :=
(card_eq : s.card = n)

lemma is_n_clique_iff : G.is_n_clique n s ↔ G.is_clique s ∧ s.card = n :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

instance [decidable_eq α] [decidable_rel G.adj] {n : ℕ} {s : finset α} :
  decidable (G.is_n_clique n s) :=
decidable_of_iff' _ G.is_n_clique_iff

variables {G H}

lemma is_n_clique.mono (h : G ≤ H) : G.is_n_clique n s → H.is_n_clique n s :=
by { simp_rw is_n_clique_iff, exact and.imp_left (is_clique.mono h) }

end simple_graph
