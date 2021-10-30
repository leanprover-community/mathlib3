/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .regularity_lemma
import combinatorics.simple_graph.subgraph

/-!
# Triangle counting lemma
-/

open finset fintype
open_locale big_operators

variables {α : Type*} (G : simple_graph α)

namespace simple_graph

-- def is_triangle (a b c : α) : Prop := G.adj a b ∧ G.adj b c ∧ G.adj c a

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
def is_n_clique (n : ℕ) (s : finset α) : Prop := s.card = n ∧ (s : set α).pairwise_on G.adj

instance [decidable_eq α] [decidable_rel G.adj] {n} {s : finset α} :
  decidable (G.is_n_clique n s) :=
decidable_of_iff (s.card = n ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.adj x y)
  (by simp [simple_graph.is_n_clique, set.pairwise_on])

def no_triangles := ∀ t, ¬ G.is_n_clique 3 t

lemma bot_no_triangles : (⊥ : simple_graph α).no_triangles :=
begin
  rintro t ⟨ht₁, ht₂⟩,
  have : 1 < t.card,
  { rw ht₁,
    norm_num },
  rw finset.one_lt_card at this,
  obtain ⟨x, hx, y, hy, hxy⟩ := this,
  apply ht₂ _ hx _ hy hxy,
end

variables [fintype α] [decidable_eq α]

def triangle_finset [decidable_rel G.adj] : finset (finset α) :=
  (powerset_len 3 univ).filter (G.is_n_clique 3)

lemma mem_triangle_finset [decidable_rel G.adj] (s : finset α) :
  s ∈ G.triangle_finset ↔ s.card = 3 ∧ (s : set α).pairwise_on G.adj :=
by simp [triangle_finset, mem_powerset_len, is_n_clique]

lemma triangle_finset_empty_iff [decidable_rel G.adj] :
  G.triangle_finset = ∅ ↔ G.no_triangles :=
by simp only [mem_triangle_finset, eq_empty_iff_forall_not_mem, no_triangles, is_n_clique]

open_locale classical

/-- Removes one edge from each victim to kill them. -/
def kill_finsets (G : simple_graph α) (victims : finset (finset α)) : simple_graph α :=
begin
  sorry
end

lemma kill_finsets_le {G : simple_graph α} {victims : finset (finset α)} :
  G.kill_finsets victims ≤ G :=
sorry

lemma card_kill_finsets (G : simple_graph α) {victims : finset (finset α)}
  (yet_alive : ∀ ⦃s : finset α⦄, s ∈ victims → 2 ≤ s.card) :
  (G.kill_finsets victims).edge_finset.card = G.edge_finset.card - victims.card :=
begin
  sorry
end

def triangle_free_far (G : simple_graph α) (ε : ℝ) : Prop :=
  ∀ (G' ≤ G), G'.no_triangles → ε * (card α)^2 ≤ (G.edge_finset.card - G'.edge_finset.card : ℝ)

lemma eps_eq_zero_of_no_triangles [nonempty α] {ε : ℝ} (hε : 0 ≤ ε) (hG : G.triangle_free_far ε)
  (hG' : G.no_triangles) :
  ε = 0 :=
begin
  have := hG G le_rfl hG',
  simp only [sub_self] at this,
  apply (nonpos_of_mul_nonpos_right this (sq_pos_of_ne_zero _ _)).antisymm hε,
  simp only [nat.cast_ne_zero, ←pos_iff_ne_zero, fintype.card_pos],
end

variables {G} [nonempty α] {ε : ℝ}

lemma triangle_free_far_of_pairwise_disjoint (hε : ε * (card α)^2 ≤ G.triangle_finset.card)
  (ht : (G.triangle_finset : set (finset α)).pairwise_disjoint) :
  G.triangle_free_far ε :=
begin
  refine λ H hHG hH, hε.trans _,
  rw [le_sub_iff_add_le, ←nat.cast_add, nat.cast_le],
  sorry
end


lemma triangle_free_far.le_card_triangle_finset (hG : G.triangle_free_far ε) :
  ε * (card α)^2 ≤ G.triangle_finset.card :=
begin
  refine (hG (G.kill_finsets G.triangle_finset) kill_finsets_le _).trans _,
  sorry,
  sorry
end

lemma triangle_free_far.not_no_triangles (hG : G.triangle_free_far ε) (hε : 0 < ε) :
  ¬ G.no_triangles :=
λ hG', hε.ne' (eps_eq_zero_of_no_triangles G hε.le hG hG')

lemma triangle_free_far.triangle_finset_card_pos (hG : G.triangle_free_far ε) (hε : 0 < ε) :
  0 < G.triangle_finset.card :=
begin
  rw [finset.card_pos, nonempty_iff_ne_empty, ne.def, triangle_finset_empty_iff],
  apply hG.not_no_triangles hε,
end

end simple_graph
