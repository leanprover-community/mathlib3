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
* `simple_graph.clique_finset`: Finset of `n`-cliques of a graph.
* `simple_graph.clique_free`: Predicate for a graph to have no `n`-cliques.

## TODO

* Clique numbers
* Going back and forth between cliques and complete subgraphs or embeddings of complete graphs.
-/

open finset fintype

namespace simple_graph
variables {α : Type*} (G H : simple_graph α)

/-! ### Cliques -/

section clique
variables {s t : set α}

/-- A clique in a graph is a set of vertices which are pairwise connected. -/
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

end n_clique

/-! ### Graphs without cliques -/

section clique_free
variables {n : ℕ}

/-- `G.clique_free n` means that `G` has no `n`-cliques. -/
def clique_free (n : ℕ) : Prop := ∀ t, ¬ G.is_n_clique n t

variables {G H}

lemma clique_free_bot (h : 2 ≤ n) : (⊥ : simple_graph α).clique_free n :=
begin
  rintro t ht,
  rw is_n_clique_bot_iff at ht,
  linarith,
end

lemma clique_free.mono (h : G ≤ H) : H.clique_free n → G.clique_free n :=
forall_imp $ λ s, mt $ is_n_clique.mono h

end clique_free

/-! ### Finset of cliques -/

section clique_finset
variables (G) [fintype α] [decidable_eq α] [decidable_rel G.adj] {n : ℕ} {a b c : α} {s : finset α}

/-- The `n`-cliques in a graph as a finset. -/
def clique_finset (n : ℕ) : finset (finset α) := univ.filter $ G.is_n_clique n

lemma mem_clique_finset_iff (s : finset α) : s ∈ G.clique_finset n ↔ G.is_n_clique n s :=
mem_filter.trans $ and_iff_right $ mem_univ _

lemma triple_mem_clique_finset_iff :
  {a, b, c} ∈ G.clique_finset 3 ↔ G.adj a b ∧ G.adj a c ∧ G.adj b c :=
begin
  rw [mem_clique_finset_iff, is_n_clique_iff, is_clique_iff],
  simp only [coe_insert, coe_singleton, set.pairwise_insert_of_symmetric G.symm,
    set.pairwise_singleton, true_and, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, ne.def],
  split,
  { rintro ⟨⟨hbc, hab, hac⟩, h⟩,
    refine ⟨hab _, hac _, hbc _⟩;
    { rintro rfl,
      simp only [insert_idem, insert_singleton_comm, insert_singleton_self_eq] at h,
      exact h.not_lt (nat.lt_succ_iff.2 $ card_insert_le _ _) } },
  { rintro ⟨hab, hac, hbc⟩,
    refine ⟨⟨λ _, hbc, λ _, hab, λ _, hac⟩, _⟩,
    rw card_eq_three,
    exact ⟨_, _, _, G.ne_of_adj hab, G.ne_of_adj hac, G.ne_of_adj hbc, rfl⟩ }
end

lemma mem_clique_finset_iff' :
  s ∈ G.clique_finset 3 ↔ ∃ a b c, G.adj a b ∧ G.adj a c ∧ G.adj b c ∧ s = {a, b, c} :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.1 ((G.mem_clique_finset_iff s).1 h).2,
    refine ⟨a, b, c, _⟩,
    rw triple_mem_clique_finset_iff at h,
    tauto },
  { rintro ⟨a, b, c, hab, hbc, hca, rfl⟩,
    exact G.triple_mem_clique_finset_iff.2 ⟨hab, hbc, hca⟩ }
end

@[simp] lemma clique_finset_eq_empty_iff : G.clique_finset n = ∅ ↔ G.clique_free n :=
by simp_rw [clique_free, eq_empty_iff_forall_not_mem, mem_clique_finset_iff]

alias clique_finset_eq_empty_iff ↔ _ simple_graph.clique_free.clique_finset

attribute [protected] clique_free.clique_finset

variables {G} [decidable_rel H.adj]

lemma clique_finset_mono (h : G ≤ H) : G.clique_finset n ⊆ H.clique_finset n :=
monotone_filter_right _ $ λ _, is_n_clique.mono h

end clique_finset
end simple_graph
