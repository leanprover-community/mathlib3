/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import data.finset.pairwise
import data.finset.preimage

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
* Dualise all the API to get independent sets
-/

open finset fintype function

namespace simple_graph
variables {α β : Type*} (G H : simple_graph α)

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

variables {G H} {a b : α}

@[simp] lemma is_clique_empty : G.is_clique ∅ := set.pairwise_empty _
@[simp] lemma is_clique_singleton (a : α) : G.is_clique {a} := set.pairwise_singleton _ _

lemma is_clique_pair : G.is_clique {a, b} ↔ a ≠ b → G.adj a b :=
set.pairwise_pair_of_symmetric G.symm

@[simp] lemma is_clique_insert :
  G.is_clique (insert a s) ↔ G.is_clique s ∧ ∀ b ∈ s, a ≠ b → G.adj a b :=
set.pairwise_insert_of_symmetric G.symm

lemma is_clique_insert_of_not_mem (ha : a ∉ s) :
  G.is_clique (insert a s) ↔ G.is_clique s ∧ ∀ b ∈ s, G.adj a b :=
set.pairwise_insert_of_symmetric_of_not_mem G.symm ha

lemma is_clique.insert (hs : G.is_clique s) (h : ∀ b ∈ s, a ≠ b → G.adj a b) :
  G.is_clique (insert a s) :=
hs.insert_of_symmetric G.symm h

lemma is_clique.mono (h : G ≤ H) : G.is_clique s → H.is_clique s := set.pairwise.mono' h
lemma is_clique.subset (h : t ⊆ s) : G.is_clique s → G.is_clique t := set.pairwise.mono h

protected lemma is_clique.map {G : simple_graph α} {s : set α} (h : G.is_clique s) {f : α ↪ β} :
  (G.map f).is_clique (f '' s) :=
by { rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab,
  exact ⟨a, b, h ha hb $ ne_of_apply_ne _ hab, rfl, rfl⟩ }

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

variables {G H} {a b c : α}

@[simp] lemma is_n_clique_empty : G.is_n_clique n ∅ ↔ n = 0 := by simp [is_n_clique_iff, eq_comm]
@[simp] lemma is_n_clique_singleton : G.is_n_clique n {a} ↔ n = 1 :=
by simp [is_n_clique_iff, eq_comm]

lemma is_n_clique.mono (h : G ≤ H) : G.is_n_clique n s → H.is_n_clique n s :=
by { simp_rw is_n_clique_iff, exact and.imp_left (is_clique.mono h) }

protected lemma is_n_clique.map (h : G.is_n_clique n s) {f : α ↪ β} :
  (G.map f).is_n_clique n (s.map f) :=
⟨by { rw coe_map, exact h.1.map}, (card_map _).trans h.2⟩

@[simp] lemma is_n_clique_bot_iff : (⊥ : simple_graph α).is_n_clique n s ↔ n ≤ 1 ∧ s.card = n :=
begin
  rw [is_n_clique_iff, is_clique_bot_iff],
  refine and_congr_left _,
  rintro rfl,
  exact card_le_one.symm,
end

@[simp] lemma is_n_clique_zero : G.is_n_clique 0 s ↔ s = ∅ :=
by { simp only [is_n_clique_iff, finset.card_eq_zero, and_iff_right_iff_imp], rintro rfl, simp }

@[simp] lemma is_n_clique_one : G.is_n_clique 1 s ↔ ∃ a, s = {a} :=
by { simp only [is_n_clique_iff, card_eq_one, and_iff_right_iff_imp], rintro ⟨a, rfl⟩, simp }

variables [decidable_eq α]

lemma is_n_clique.insert (hs : G.is_n_clique n s) (h : ∀ b ∈ s, G.adj a b) :
  G.is_n_clique (n + 1) (insert a s) :=
begin
  split,
  { push_cast,
    exact hs.1.insert (λ b hb _, h _ hb) },
  { rw [card_insert_of_not_mem (λ ha, (h _ ha).ne rfl), hs.2] }
end

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

@[simp] lemma clique_free_bot (h : 2 ≤ n) : (⊥ : simple_graph α).clique_free n :=
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

@[simp] lemma clique_free_two : G.clique_free 2 ↔ G = ⊥ :=
begin
  classical,
  split,
  { simp_rw [←edge_set_eq_empty, set.eq_empty_iff_forall_not_mem, sym2.forall, mem_edge_set],
    exact λ h a b hab, h _ ⟨by simpa [hab.ne], card_doubleton hab.ne⟩ },
  { rintro rfl,
    exact clique_free_bot le_rfl }
end

end clique_free

section clique_free_on
variables {s s₁ s₂ : set α} {t : finset α} {a b : α} {m n : ℕ}

/-- `G.clique_free_on s n` means that `G` has no `n`-cliques contained in `s`. -/
def clique_free_on (G : simple_graph α) (s : set α) (n : ℕ) : Prop :=
∀ ⦃t⦄, ↑t ⊆ s → ¬G.is_n_clique n t

lemma clique_free_on.subset (hs : s₁ ⊆ s₂) (h₂ : G.clique_free_on s₂ n) : G.clique_free_on s₁ n :=
λ t hts, h₂ $ hts.trans hs

lemma clique_free_on.mono (hmn : m ≤ n) (hG : G.clique_free_on s m) : G.clique_free_on s n :=
begin
  rintro t hts ht,
  obtain ⟨u, hut, hu⟩ := t.exists_smaller_set _ (hmn.trans ht.card_eq.ge),
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.clique.subset hut, hu⟩,
end

lemma clique_free_on.anti (hGH : G ≤ H) (hH : H.clique_free_on s n) : G.clique_free_on s n :=
λ t hts ht, hH hts $ ht.mono hGH

@[simp] lemma clique_free_on_empty : G.clique_free_on ∅ n ↔ n ≠ 0 :=
by simp [clique_free_on, set.subset_empty_iff]

@[simp] lemma clique_free_on_singleton : G.clique_free_on {a} n ↔ 1 < n :=
by obtain _ | _ | n := n; simp [clique_free_on, set.subset_singleton_iff_eq]

@[simp] lemma clique_free_on_univ : G.clique_free_on set.univ n ↔ G.clique_free n :=
by simp [clique_free, clique_free_on]

protected lemma clique_free.clique_free_on (hG : G.clique_free n) : G.clique_free_on s n :=
λ t _, hG _

lemma clique_free_on_of_card_lt {s : finset α} (h : s.card < n) : G.clique_free_on s n :=
λ t hts ht, h.not_le $ ht.2.symm.trans_le $ card_mono hts

--TOOD: Restate using `simple_graph.indep_set` once we have it
@[simp] lemma clique_free_on_two : G.clique_free_on s 2 ↔ s.pairwise G.adjᶜ :=
begin
  classical,
  refine ⟨λ h a ha b hb _ hab, h _ ⟨by simpa [hab.ne], card_doubleton hab.ne⟩, _⟩,
  { push_cast,
    exact set.insert_subset.2 ⟨ha, set.singleton_subset_iff.2 hb⟩ },
  simp only [clique_free_on, is_n_clique_iff, card_eq_two, coe_subset, not_and, not_exists],
  rintro h t hst ht a b hab rfl,
  simp only [coe_insert, coe_singleton, set.insert_subset, set.singleton_subset_iff] at hst,
  refine h hst.1 hst.2 hab (ht _ _ hab); simp,
end

lemma clique_free_on.of_succ (hs : G.clique_free_on s (n + 1)) (ha : a ∈ s) :
  G.clique_free_on (s ∩ G.neighbor_set a) n :=
begin
  classical,
  refine λ t hts ht, hs _ (ht.insert $ λ b hb, (hts hb).2),
  push_cast,
  exact set.insert_subset.2 ⟨ha, hts.trans $ set.inter_subset_left _ _⟩,
end

end clique_free_on

/-! ### Set of cliques -/

section clique_set
variables (G) {n : ℕ} {a b c : α} {s : finset α}

/-- The `n`-cliques in a graph as a set. -/
def clique_set (n : ℕ) : set (finset α) := {s | G.is_n_clique n s}

@[simp] lemma mem_clique_set_iff : s ∈ G.clique_set n ↔ G.is_n_clique n s := iff.rfl

@[simp] lemma clique_set_eq_empty_iff : G.clique_set n = ∅ ↔ G.clique_free n :=
by simp_rw [clique_free, set.eq_empty_iff_forall_not_mem, mem_clique_set_iff]

variables {G H}

protected lemma clique_free.clique_set : G.clique_free n → G.clique_set n = ∅ :=
G.clique_set_eq_empty_iff.2

@[mono] lemma clique_set_mono (h : G ≤ H) : G.clique_set n ⊆ H.clique_set n :=
λ _, is_n_clique.mono h

lemma clique_set_mono' (h : G ≤ H) : G.clique_set ≤ H.clique_set := λ _, clique_set_mono h

@[simp] lemma clique_set_zero (G : simple_graph α) : G.clique_set 0 = {∅} :=
set.ext $ λ s, by simp

@[simp] lemma clique_set_one (G : simple_graph α) : G.clique_set 1 = set.range singleton :=
set.ext $ λ s, by simp [eq_comm]

@[simp] lemma clique_set_bot (hn : 1 < n) : (⊥ : simple_graph α).clique_set n = ∅ :=
(clique_free_bot hn).clique_set

@[simp] lemma clique_set_map (hn : n ≠ 1) (G : simple_graph α) (f : α ↪ β) :
  (G.map f).clique_set n = map f '' G.clique_set n :=
begin
  ext s,
  split,
  { rintro ⟨hs, rfl⟩,
    have hs' : (s.preimage f $ f.injective.inj_on _).map f = s,
    { classical,
      rw [map_eq_image, image_preimage, filter_true_of_mem],
      rintro a ha,
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (hn.lt_of_le' $ finset.card_pos.2 ⟨a, ha⟩) a,
      obtain ⟨c, _, _, hc, _⟩ := hs ha hb hba.symm,
      exact ⟨c, hc⟩ },
    refine ⟨s.preimage f $ f.injective.inj_on _, ⟨_, by rw [←card_map f, hs']⟩, hs'⟩,
    rw coe_preimage,
    exact λ a ha b hb hab, map_adj_apply.1 (hs ha hb $ f.injective.ne hab) },
  { rintro ⟨s, hs, rfl⟩,
    exact is_n_clique.map hs }
end

@[simp] lemma clique_set_map_of_equiv (G : simple_graph α) (e : α ≃ β) (n : ℕ) :
  (G.map e.to_embedding).clique_set n = map e.to_embedding '' G.clique_set n :=
begin
  obtain rfl | hn := eq_or_ne n 1,
  { ext,
    simp [e.exists_congr_left] },
  { exact clique_set_map hn _ _ }
end


end clique_set

/-! ### Finset of cliques -/

section clique_finset
variables (G) [fintype α] [decidable_eq α] [decidable_rel G.adj] {n : ℕ} {a b c : α} {s : finset α}

/-- The `n`-cliques in a graph as a finset. -/
def clique_finset (n : ℕ) : finset (finset α) := univ.filter $ G.is_n_clique n

@[simp] lemma mem_clique_finset_iff : s ∈ G.clique_finset n ↔ G.is_n_clique n s :=
mem_filter.trans $ and_iff_right $ mem_univ _

@[simp, norm_cast] lemma coe_clique_finset (n : ℕ) :
  (G.clique_finset n : set (finset α)) = G.clique_set n :=
set.ext $ λ _, mem_clique_finset_iff _

@[simp] lemma clique_finset_eq_empty_iff : G.clique_finset n = ∅ ↔ G.clique_free n :=
by simp_rw [clique_free, eq_empty_iff_forall_not_mem, mem_clique_finset_iff]

alias clique_finset_eq_empty_iff ↔ _ _root_.simple_graph.clique_free.clique_finset

attribute [protected] clique_free.clique_finset

variables {G}

lemma card_clique_finset_le : (G.clique_finset n).card ≤ (card α).choose n :=
begin
  rw [←card_univ, ←card_powerset_len],
  refine card_mono (λ s, _),
  simpa [mem_powerset_len_univ_iff] using is_n_clique.card_eq,
end

variables [decidable_rel H.adj]

@[mono] lemma clique_finset_mono (h : G ≤ H) : G.clique_finset n ⊆ H.clique_finset n :=
monotone_filter_right _ $ λ _, is_n_clique.mono h

variables [fintype β] [decidable_eq β] (G)

@[simp] lemma clique_finset_map (f : α ↪ β) (hn : n ≠ 1) :
  (G.map f).clique_finset n = (G.clique_finset n).map ⟨map f, finset.map_injective _⟩ :=
coe_injective $
  by simp_rw [coe_clique_finset, clique_set_map hn, coe_map, coe_clique_finset, embedding.coe_fn_mk]

@[simp] lemma clique_finset_map_of_equiv (e : α ≃ β) (n : ℕ) :
  (G.map e.to_embedding).clique_finset n =
    (G.clique_finset n).map ⟨map e.to_embedding, finset.map_injective _⟩ :=
coe_injective $ by push_cast; exact clique_set_map_of_equiv _ _ _

end clique_finset
end simple_graph
