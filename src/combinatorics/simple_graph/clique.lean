/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import data.finset.pairwise

/-!
# Graph cliques

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines cliques in simple graphs. A clique is a set of vertices that are pairwise
adjacent.

## Main declarations

* `simple_graph.is_clique`: Predicate for a set of vertices to be a clique.
* `simple_graph.is_n_clique`: Predicate for a set of vertices to be a `n`-clique.
* `simple_graph.clique_finset`: Finset of `n`-cliques of a graph.
* `simple_graph.clique_free`: Predicate for a graph to have no `n`-cliques.

## TODO

* Clique numbers
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

/-- A clique is a set of vertices whose induced graph is complete. -/
lemma is_clique_iff_induce_eq : G.is_clique s ↔ G.induce s = ⊤ :=
begin
  rw is_clique_iff,
  split,
  { intro h,
    ext ⟨v, hv⟩ ⟨w, hw⟩,
    simp only [comap_adj, subtype.coe_mk, top_adj, ne.def, subtype.mk_eq_mk],
    exact ⟨adj.ne, h hv hw⟩, },
  { intros h v hv w hw hne,
    have : (G.induce s).adj ⟨v, hv⟩ ⟨w, hw⟩ = _ := rfl,
    conv_lhs at this { rw h },
    simpa [hne], }
end

instance [decidable_eq α] [decidable_rel G.adj] {s : finset α} : decidable (G.is_clique s) :=
decidable_of_iff' _ G.is_clique_iff

variables {G H}

lemma is_clique.mono (h : G ≤ H) : G.is_clique s → H.is_clique s :=
by { simp_rw is_clique_iff, exact set.pairwise.mono' h }

lemma is_clique.subset (h : t ⊆ s) : G.is_clique s → G.is_clique t :=
by { simp_rw is_clique_iff, exact set.pairwise.mono h }

@[simp] lemma is_clique_bot_iff : (⊥ : simple_graph α).is_clique s ↔ (s : set α).subsingleton :=
set.pairwise_bot_iff

alias is_clique_bot_iff ↔ is_clique.subsingleton _

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

variables {G H} {s : finset α}

lemma is_n_clique.not_clique_free (hG : G.is_n_clique n s) : ¬ G.clique_free n := λ h, h _ hG

lemma not_clique_free_of_top_embedding {n : ℕ}
  (f : (⊤ : simple_graph (fin n)) ↪g G) : ¬ G.clique_free n :=
begin
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, not_forall, not_not],
  use finset.univ.map f.to_embedding,
  simp only [card_map, finset.card_fin, eq_self_iff_true, and_true],
  ext ⟨v, hv⟩ ⟨w, hw⟩,
  simp only [coe_map, rel_embedding.coe_fn_to_embedding, set.mem_image,
    coe_univ, set.mem_univ, true_and] at hv hw,
  obtain ⟨v', rfl⟩ := hv,
  obtain ⟨w', rfl⟩ := hw,
  simp only [f.map_adj_iff, comap_adj, function.embedding.coe_subtype, subtype.coe_mk, top_adj,
    ne.def, subtype.mk_eq_mk],
  exact (function.embedding.apply_eq_iff_eq _ _ _).symm.not,
end

/-- An embedding of a complete graph that witnesses the fact that the graph is not clique-free. -/
noncomputable
def top_embedding_of_not_clique_free {n : ℕ} (h : ¬ G.clique_free n) :
  (⊤ : simple_graph (fin n)) ↪g G :=
begin
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, not_forall, not_not] at h,
  obtain ⟨ha, hb⟩ := h.some_spec,
  have : (⊤ : simple_graph (fin h.some.card)) ≃g (⊤ : simple_graph h.some),
  { apply iso.complete_graph,
    simpa using (fintype.equiv_fin h.some).symm },
  rw ← ha at this,
  convert (embedding.induce ↑h.some).comp this.to_embedding;
  exact hb.symm,
end

lemma not_clique_free_iff (n : ℕ) :
  ¬ G.clique_free n ↔ nonempty ((⊤ : simple_graph (fin n)) ↪g G) :=
begin
  split,
  { exact λ h, ⟨top_embedding_of_not_clique_free h⟩ },
  { rintro ⟨f⟩,
    exact not_clique_free_of_top_embedding f },
end

lemma clique_free_iff {n : ℕ} :
  G.clique_free n ↔ is_empty ((⊤ : simple_graph (fin n)) ↪g G) :=
by rw [← not_iff_not, not_clique_free_iff, not_is_empty_iff]

lemma not_clique_free_card_of_top_embedding [fintype α] (f : (⊤ : simple_graph α) ↪g G) :
  ¬ G.clique_free (card α) :=
begin
  rw [not_clique_free_iff],
  use (iso.complete_graph (fintype.equiv_fin α)).symm.to_embedding.trans f,
end

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

/-- See `simple_graph.clique_free_chromatic_number_succ` for a tighter bound. -/
lemma clique_free_of_card_lt [fintype α] (hc : card α < n) : G.clique_free n :=
begin
  by_contra h,
  refine nat.lt_le_antisymm hc _,
  rw [clique_free_iff, not_is_empty_iff] at h,
  simpa using fintype.card_le_of_embedding h.some.to_embedding,
end

end clique_free

/-! ### Set of cliques -/

section clique_set
variables (G) {n : ℕ} {a b c : α} {s : finset α}

/-- The `n`-cliques in a graph as a set. -/
def clique_set (n : ℕ) : set (finset α) := {s | G.is_n_clique n s}

lemma mem_clique_set_iff : s ∈ G.clique_set n ↔ G.is_n_clique n s := iff.rfl

@[simp] lemma clique_set_eq_empty_iff : G.clique_set n = ∅ ↔ G.clique_free n :=
by simp_rw [clique_free, set.eq_empty_iff_forall_not_mem, mem_clique_set_iff]

alias clique_set_eq_empty_iff ↔ _ clique_free.clique_set

attribute [protected] clique_free.clique_set

variables {G H}

@[mono] lemma clique_set_mono (h : G ≤ H) : G.clique_set n ⊆ H.clique_set n :=
λ _, is_n_clique.mono h

lemma clique_set_mono' (h : G ≤ H) : G.clique_set ≤ H.clique_set := λ _, clique_set_mono h

end clique_set

/-! ### Finset of cliques -/

section clique_finset
variables (G) [fintype α] [decidable_eq α] [decidable_rel G.adj] {n : ℕ} {a b c : α} {s : finset α}

/-- The `n`-cliques in a graph as a finset. -/
def clique_finset (n : ℕ) : finset (finset α) := univ.filter $ G.is_n_clique n

lemma mem_clique_finset_iff : s ∈ G.clique_finset n ↔ G.is_n_clique n s :=
mem_filter.trans $ and_iff_right $ mem_univ _

@[simp] lemma coe_clique_finset (n : ℕ) : (G.clique_finset n : set (finset α)) = G.clique_set n :=
set.ext $ λ _, mem_clique_finset_iff _

@[simp] lemma clique_finset_eq_empty_iff : G.clique_finset n = ∅ ↔ G.clique_free n :=
by simp_rw [clique_free, eq_empty_iff_forall_not_mem, mem_clique_finset_iff]

alias clique_finset_eq_empty_iff ↔ _ _root_.simple_graph.clique_free.clique_finset

attribute [protected] clique_free.clique_finset

variables {G} [decidable_rel H.adj]

@[mono] lemma clique_finset_mono (h : G ≤ H) : G.clique_finset n ⊆ H.clique_finset n :=
monotone_filter_right _ $ λ _, is_n_clique.mono h

end clique_finset
end simple_graph
