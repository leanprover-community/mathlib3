/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import data.real.basic

/-!
# Triangles in graphs

This file defines triangles in simple graphs.

## Main declarations

* `simple_graph.is_n_clique`
* `simple_graph.no_triangles`
* `simple_graph.triangle_finset`
-/

open finset fintype
open_locale big_operators

variables {α : Type*} (G : simple_graph α)

namespace simple_graph

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
def is_n_clique (n : ℕ) (s : finset α) : Prop := s.card = n ∧ (s : set α).pairwise G.adj

instance [decidable_eq α] [decidable_rel G.adj] {n} {s : finset α} :
  decidable (G.is_n_clique n s) :=
decidable_of_iff (s.card = n ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.adj x y)
  (by simp [simple_graph.is_n_clique, set.pairwise])

/-- `G` has no triangles. -/
def no_triangles := ∀ t, ¬ G.is_n_clique 3 t

lemma bot_no_triangles : (⊥ : simple_graph α).no_triangles :=
begin
  rintro t ⟨ht₁, ht₂⟩,
  have : 1 < t.card,
  { rw ht₁,
    norm_num },
  rw finset.one_lt_card at this,
  obtain ⟨x, hx, y, hy, hxy⟩ := this,
  apply ht₂ hx hy hxy,
end

section triangle_finset
variables [fintype α] [decidable_eq α] [decidable_rel G.adj]

/-- The triangles in a graph as a finset. -/
def triangle_finset : finset (finset α) :=
(powerset_len 3 univ).filter $ G.is_n_clique 3

lemma mem_triangle_finset (s : finset α) :
  s ∈ G.triangle_finset ↔ s.card = 3 ∧ (s : set α).pairwise G.adj :=
by simp [triangle_finset, mem_powerset_len, is_n_clique]

lemma mem_triangle_finset' (s : finset α) :
  s ∈ G.triangle_finset ↔ G.is_n_clique 3 s :=
G.mem_triangle_finset s

lemma mem_triangle_finset'' (x y z : α) :
  {x, y, z} ∈ G.triangle_finset ↔ G.adj x y ∧ G.adj x z ∧ G.adj y z :=
begin
  rw [mem_triangle_finset],
  simp only [coe_insert, coe_singleton, set.pairwise_insert_of_symmetric G.symm,
    set.pairwise_singleton, true_and, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, ne.def],
  split,
  { rintro ⟨h, yz, xy, xz⟩,
    have : x ≠ y ∧ x ≠ z ∧ y ≠ z,
    { refine ⟨_, _, _⟩;
      { rintro rfl,
        simp only [insert_idem, insert_singleton_comm, insert_singleton_self_eq] at h,
        apply ne_of_lt _ h,
        rw nat.lt_succ_iff,
        apply card_insert_le _ _ } },
    tauto },
  rintro ⟨xy, xz, yz⟩,
  refine ⟨_, λ _, yz, λ _, xy, λ _, xz⟩,
  rw card_eq_three,
  exact ⟨_, _, _, G.ne_of_adj xy, G.ne_of_adj xz, G.ne_of_adj yz, rfl⟩,
end

lemma mem_triangle_finset''' {s : finset α} :
  s ∈ G.triangle_finset ↔ ∃ x y z, G.adj x y ∧ G.adj x z ∧ G.adj y z ∧ s = {x,y,z} :=
begin
  split,
  { intro h,
    obtain ⟨x, y, z, -, -, -, rfl⟩ := card_eq_three.1 ((G.mem_triangle_finset s).1 h).1,
    refine ⟨x, y, z, _⟩,
    rw mem_triangle_finset'' at h,
    tauto },
  rintro ⟨x, y, z, _, _, _, rfl⟩,
  rw mem_triangle_finset'',
  tauto
end

lemma triangle_finset_empty_iff : G.triangle_finset = ∅ ↔ G.no_triangles :=
by simp only [mem_triangle_finset, eq_empty_iff_forall_not_mem, no_triangles, is_n_clique]

end triangle_finset

open_locale classical

section triangle_free_far
variables [fintype α]

/-- A simple graph is `ε`-triangle-free far if one must remove a density of `ε` edges to make it
triangle-free. -/
def triangle_free_far (G : simple_graph α) (ε : ℝ) : Prop :=
∀ G' ≤ G, G'.no_triangles → ε * (card α)^2 ≤ (G.edge_finset.card - G'.edge_finset.card : ℝ)

lemma has_triangle_of_few_edges_removed {ε : ℝ} {G' : simple_graph α} (hG' : G' ≤ G)
  (hG : G.triangle_free_far ε)
  (hcard : (G.edge_finset.card - G'.edge_finset.card : ℝ) < ε * card α^2) :
  ∃ t, t ∈ G'.triangle_finset :=
begin
  apply nonempty_of_ne_empty,
  rw [ne.def, triangle_finset_empty_iff],
  intro hG'',
  apply not_le_of_lt hcard (hG _ hG' hG''),
end

lemma eps_eq_zero_of_no_triangles [nonempty α] {ε : ℝ} (hε : 0 ≤ ε) (hG : G.triangle_free_far ε)
  (hG' : G.no_triangles) :
  ε = 0 :=
begin
  have := hG G le_rfl hG',
  simp only [sub_self] at this,
  apply (nonpos_of_mul_nonpos_right this (sq_pos_of_ne_zero _ _)).antisymm hε,
  simp only [nat.cast_ne_zero, ←pos_iff_ne_zero, fintype.card_pos],
end

end triangle_free_far
end simple_graph
