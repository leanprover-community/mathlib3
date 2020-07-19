/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import .bigraph
import .simple_graph

open_locale classical
noncomputable theory

open simple_graph bigraph

universes u
variables {V : Type u} [fintype V] [inhabited V] (G : simple_graph V)

def path_bigraph (A B : finset V) : bigraph V V :=
  bigraph.mk A B G.E

variables {G}

lemma path_bigraph_swap {A B : finset V} :
  (path_bigraph G A B).swap = path_bigraph G B A:=
by { ext, { refl }, { refl }, split; apply G.undirected }

lemma left_fiber_eq_nbrs_inter_A {A B : finset V} {v : V} (hv : v ∈ B) :
  left_fiber (path_bigraph G A B) v = A ∩ (neighbors G v):=
begin
  ext, simp only [neighbor_iff_adjacent, mem_left_fiber, finset.mem_inter],
  erw edge_symm, cc,
end

lemma right_fiber_eq_nbrs_inter_B {A B : finset V} {v : V} (hv : v ∈ A):
right_fiber (path_bigraph G A B) v = B ∩ (neighbors G v):=
by rwa [← left_fiber_swap, path_bigraph_swap, left_fiber_eq_nbrs_inter_A]

variables {d : ℕ}

lemma reg_card_count_2 (hd : regular_graph G d) (v : V) :
card_edges (path_bigraph G (neighbors G v) {v}) = d :=
begin
  rw ← hd v, apply card_edges_of_runique, rw right_unique_one_reg,
  intros a ha, erw right_fiber_eq_nbrs_inter_B ha,
  suffices : neighbors G a ∩ {v} = {v}, rw [finset.inter_comm], simp [this],
  apply finset.inter_singleton_of_mem,
  rwa [neighbor_iff_adjacent, edge_symm, ← neighbor_iff_adjacent],
end

lemma reg_card_count_3 (hd : regular_graph G d) (v : V) :
card_edges (path_bigraph G (neighbors G v) finset.univ) = d * d :=
begin
  unfold regular_graph degree at hd,
  transitivity d * (neighbors G v).card,
  swap, { rw hd },
  apply card_edges_of_rreg,
  intros a _, convert hd a,
end
