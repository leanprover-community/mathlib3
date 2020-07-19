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
begin
  ext, { refl }, { refl },
  split; apply G.undirected,
end

lemma left_fiber_eq_nbrs_inter_A {A B : finset V} {v : V} :
  v ∈ B → left_fiber (path_bigraph G A B) v = A ∩ (neighbors G v):=
begin
  intro vB, ext,
  simp only [neighbor_iff_adjacent, mem_left_fiber, finset.mem_inter],
  change a ∈ A ∧ G.E a v ↔ a ∈ A ∧ G.E v a,
  have h : G.E a v ↔ G.E v a, {split; apply G.undirected},
  rw h,
end

lemma right_fiber_eq_nbrs_inter_B {A B : finset V} {v : V} (hv : v ∈ A):
right_fiber (path_bigraph G A B) v = B ∩ (neighbors G v):=
begin
  rw [← left_fiber_swap, path_bigraph_swap],
  exact left_fiber_eq_nbrs_inter_A hv,
end

variables {d : ℕ}

lemma reg_card_count_2  (hd : regular_graph G d) (v:V) :
card_edges (path_bigraph G (neighbors G v) {v}) = d :=
begin
  unfold regular_graph at hd,
  rw ← hd v,
  apply card_edges_of_runique,
  rw right_unique_one_reg,
  unfold right_regular,
  intros a ha,
  change a ∈ neighbors G v at ha,
  rw right_fiber_eq_nbrs_inter_B ha,
  have h:neighbors G a∩ {v} = {v},
  { apply finset.inter_singleton_of_mem,
    rw neighbor_iff_adjacent,
    rw neighbor_iff_adjacent at ha,
    exact G.undirected ha },
  rw [finset.inter_comm, h], simp,
end


lemma reg_card_count_3 (hd : regular_graph G d) (v:V) :
card_edges (path_bigraph G (neighbors G v) finset.univ) = d * d :=
begin
  unfold regular_graph at hd,
  unfold degree at hd,

  transitivity d * (neighbors G v).card,
  swap, { rw hd v },
  apply card_edges_of_rreg,
  intros a ha,
  rw right_fiber_eq_nbrs_inter_B,
  { rw [finset.univ_inter, hd a] },
  { exact ha },
end
