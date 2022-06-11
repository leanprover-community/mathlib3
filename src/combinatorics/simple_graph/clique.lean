/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import data.finset.pairwise

/-!
# Graph cliques

This file defines cliques in simple graphs. A clique is a set of vertices that are pairwise
adjacent.

## Main declarations

* `simple_graph.is_clique`: Predicate for a set of vertices to be a clique.
* `simple_graph.is_n_clique`: Predicate for a set of vertices to be a `n`-clique.
* `simple_graph.clique_finset`: Finset of `n`-cliques of a graph.
* `simple_graph.clique_free`: Predicate for a graph to have no `n`-cliques.

## TODO

* Clique numbers
* Going back and forth between cliques and complete subgraphs or embeddings of complete graphs.
* Do we need `clique_set`, a version of `clique_finset` for infinite graphs?
-/

open finset fintype

namespace simple_graph
variables {α : Type*} (G H : simple_graph α)

/-! ### Cliques -/

section clique
variables {s t : set α}

/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
abbreviation is_clique (s : set α) : Prop := s.pairwise G.adj

lemma is_clique_iff : G.is_clique s ↔ s.pairwise G.adj := iff.rfl

instance [decidable_eq α] [decidable_rel G.adj] {s : finset α} : decidable (G.is_clique s) :=
decidable_of_iff' _ G.is_clique_iff

variables {G H}

lemma is_clique.mono (h : G ≤ H) : G.is_clique s → H.is_clique s :=
by { simp_rw is_clique_iff, exact set.pairwise.mono' h }

lemma is_clique.subset (h : t ⊆ s) : G.is_clique s → G.is_clique t :=
by { simp_rw is_clique_iff, exact set.pairwise.mono h }

@[simp] lemma is_clique_bot_iff : (⊥ : simple_graph α).is_clique s ↔ (s : set α).subsingleton :=
set.pairwise_bot_iff

alias is_clique_bot_iff ↔ simple_graph.is_clique.subsingleton _

end clique

/-! ### `n`-cliques -/

section n_clique
variables {n : ℕ} {s : finset α}

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure is_n_clique (n : ℕ) (s : finset α) : Prop :=
(clique : G.is_clique s)
(card_eq : s.card = n)

lemma is_n_clique_iff : G.is_n_clique n s ↔ G.is_clique s ∧ s.card = n :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

instance [decidable_eq α] [decidable_rel G.adj] {n : ℕ} {s : finset α} :
  decidable (G.is_n_clique n s) :=
decidable_of_iff' _ G.is_n_clique_iff

variables {G H}

lemma is_n_clique.mono (h : G ≤ H) : G.is_n_clique n s → H.is_n_clique n s :=
by { simp_rw is_n_clique_iff, exact and.imp_left (is_clique.mono h) }

@[simp] lemma is_n_clique_bot_iff : (⊥ : simple_graph α).is_n_clique n s ↔ n ≤ 1 ∧ s.card = n :=
begin
  rw [is_n_clique_iff, is_clique_bot_iff],
  refine and_congr_left _,
  rintro rfl,
  exact card_le_one.symm,
end

variables [decidable_eq α] {a b c : α}

lemma is_3_clique_triple_iff : G.is_n_clique 3 {a, b, c} ↔ G.adj a b ∧ G.adj a c ∧ G.adj b c :=
begin
  simp only [is_n_clique_iff, is_clique_iff, set.pairwise_insert_of_symmetric G.symm, coe_insert],
  have : ¬ 1 + 1 = 3 := by norm_num,
  by_cases hab : a = b; by_cases hbc : b = c; by_cases hac : a = c;
  subst_vars; simp [G.ne_of_adj, and_rotate, *],
end

lemma is_3_clique_iff :
  G.is_n_clique 3 s ↔ ∃ a b c, G.adj a b ∧ G.adj a c ∧ G.adj b c ∧ s = {a, b, c} :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.1 h.card_eq,
    refine ⟨a, b, c, _⟩,
    rw is_3_clique_triple_iff at h,
    tauto },
  { rintro ⟨a, b, c, hab, hbc, hca, rfl⟩,
    exact is_3_clique_triple_iff.2 ⟨hab, hbc, hca⟩ }
end

end n_clique

/-! ### Graphs without cliques -/

section clique_free
variables {m n : ℕ}

/-- `G.clique_free n` means that `G` has no `n`-cliques. -/
def clique_free (n : ℕ) : Prop := ∀ t, ¬ G.is_n_clique n t

variables {G H}

lemma clique_free_bot (h : 2 ≤ n) : (⊥ : simple_graph α).clique_free n :=
begin
  rintro t ht,
  rw is_n_clique_bot_iff at ht,
  linarith,
end

lemma clique_free.mono (h : m ≤ n) : G.clique_free m → G.clique_free n :=
begin
  rintro hG s hs,
  obtain ⟨t, hts, ht⟩ := s.exists_smaller_set _ (h.trans hs.card_eq.ge),
  exact hG _ ⟨hs.clique.subset hts, ht⟩,
end

lemma clique_free.anti (h : G ≤ H) : H.clique_free n → G.clique_free n :=
forall_imp $ λ s, mt $ is_n_clique.mono h

end clique_free

/-! ### Finset of cliques -/

section clique_finset
variables (G) [fintype α] [decidable_eq α] [decidable_rel G.adj] {n : ℕ} {a b c : α} {s : finset α}

/-- The `n`-cliques in a graph as a finset. -/
def clique_finset (n : ℕ) : finset (finset α) := univ.filter $ G.is_n_clique n

lemma mem_clique_finset_iff (s : finset α) : s ∈ G.clique_finset n ↔ G.is_n_clique n s :=
mem_filter.trans $ and_iff_right $ mem_univ _

@[simp] lemma clique_finset_eq_empty_iff : G.clique_finset n = ∅ ↔ G.clique_free n :=
by simp_rw [clique_free, eq_empty_iff_forall_not_mem, mem_clique_finset_iff]

alias clique_finset_eq_empty_iff ↔ _ simple_graph.clique_free.clique_finset

attribute [protected] clique_free.clique_finset

variables {G} [decidable_rel H.adj]

lemma clique_finset_mono (h : G ≤ H) : G.clique_finset n ⊆ H.clique_finset n :=
monotone_filter_right _ $ λ _, is_n_clique.mono h

end clique_finset
end simple_graph
